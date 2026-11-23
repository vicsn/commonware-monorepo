# First audit pass of the Merkle verification

A first pass through the steps of the [audit guide](../hax-dylean-audit.html), made on
2026-11-21 at revision `2d9ac6d2d` of `verify/qmdb-hax-dylean`. It was made by the author of the
guide, with tools, not by an independent reviewer: read it after forming your own view.

No finding is a flaw in a proof. Every theorem is checked by Lean and says what its statement
says. The findings are about what the statements cover, how the report words them, and the
evidence behind the links that no proof covers.

## Since the first pass

On 2026-11-22 the collision argument and the leaf target were removed. In every statement the hash
is now DyLean's hash constructor, as ProVerif and Tamarin treat a hash by default, so uniqueness
of accepted openings follows from equality of terms. `Hashing.lean`, the collision finder, the
byte-level theorems and the hashes that collided on purpose are gone. `SecurityTheorems.lean`
holds two statements, and no theorem is stated twice. After that change and the naming of
the height bound on 2026-11-23, the audited namespaces hold 98 theorems, down from 131.

| # | What the change does to the finding |
| --- | --- |
| F1 | Stands. |
| F2 | Reworded. The Lean comments, the report and the READMEs say "the extracted verifier" and name the trusted height, and the theorems lost the `production_` prefix. That this verifier is not production's stands. |
| F3 | Stands. Probes `L8` and `L9` still survive. |
| F4 | Stands. |
| F5 | No longer applies: no statement reads production's byte hashing. In its place the hash is assumed ideal, assumption A4 of the guide. That assumes more than F5 described. Nothing now reduces a broken opening to a collision, and facts about bytes are outside the model. `probe_root_is_a_leaf_input` shows one: for all seven trees it builds, the root equals the leaf digest at position 0 of a 34-byte item. |
| F6 | The README sentence is corrected. The second encoding stands. |
| F7, F9 | Stand. |
| F8 | Fixed on 2026-11-23: `check.sh` fails on any warning of the Lean build, and `sorry` is one. Probe `A6` still survives, because `probes.py` looks only at modules that stop building. |
| F10 | Fixed: the header is rewritten. |

The probes in [probes.toml](probes.toml) follow the current tree: `L1` to `L3` mutate `dyTerms`,
and `L8` adapts to the simpler client. `Closure.lean` gave way to [Dag.lean](Dag.lean), which
the guide draws as its declaration graph. The record below is otherwise as written on 2026-11-21
and describes revision `2d9ac6d2d`.

## Summary

| # | Finding | Kind | Link | Status |
| --- | --- | --- | --- | --- |
| [F1](#f1) | The verified client accepts no opening under a root built with QMDB's own hasher | broken link | L2 | open |
| [F2](#f2) | "The extracted production verifier" is a second verifier written for the proof | overclaim | L7, L2 | open |
| [F3](#f3) | Nothing shows that the client ever logs an event | weak evidence | L6 | open |
| [F4](#f4) | The proof fields that the attacker writes are never varied, and no statement covers them | weak evidence | L2 | open |
| [F5](#f5) | Production's byte hashing is read, not tested or extracted | weak evidence | L4 | open |
| [F6](#f6) | Production does not build every digest from `terms.rs` | overclaim | L0, L5 | open |
| [F7](#f7) | The toolchain cannot be rebuilt from the repository | process | L8, A1 | open |
| [F8](#f8) | The axiom audit covers two namespaces, and `sorry` elsewhere is only a warning | process | L8 | open |
| [F9](#f9) | The patch to DyLean adds a definition that the statements depend on | note | L6, A3 | accepted |
| [F10](#f10) | The header of `qmdb/README.md` is stale | process | L7 | open |

Kinds, from most to least serious: **unsound** (a theorem does not hold or is not checked; none
found), **broken link** (a link of the trust chain does not hold for a stated use), **overclaim**
(the prose says more than the statements), **weak evidence** (a link holds as far as checked, and
is checked thinly), **process**, **note**.

## How to reproduce

```bash
bash verification/check.sh                       # passes; 6 minutes on a warm machine
python3 verification/audit/probes.py             # 30 mutations, 5 minutes; all "as recorded"
python3 verification/audit/build.py --dag --check # the declaration graph is what Lean prints
cat verification/audit/probes/differential.rs >> verification/symbolic/src/qmdb/tests.rs
(cd verification/symbolic && cargo test --offline -- --nocapture probe)
git checkout verification/symbolic/src/qmdb/tests.rs
```

[probes.toml](probes.toml) holds every mutation with the verdict recorded here. Probe names
below (`R6`, `L8`, `A2`) are its entries.

## Findings

### F1

**The verified client accepts no opening under a root built with QMDB's own hasher.**
Broken link, L2.

- Claim. The target is called QMDB inclusion. The report opens with "For a historical QMDB
  Merkle proof, it is the item at a particular location in a trusted snapshot."
- Evidence. QMDB folds peaks backwards: `ROOT_BAGGING = Bagging::BackwardFold` in
  `storage/src/qmdb/mod.rs`, and `Bagging::domain` gives that policy the byte 1. The client
  hashes the root under `[MMR_DOMAIN, FORWARD_FOLD] = [0, 0]`
  (`verification/symbolic/src/qmdb.rs`). The differential tests build their trees with
  `Production::new(Bagging::ForwardFold)`, so they agree with the client and never run QMDB's
  hasher. `probe_qmdb_hasher` builds trees of 1 to 64 leaves with
  `commonware_storage::qmdb::hasher()`: of 127 honest openings production accepts 127 and the
  client accepts 0.
- Impact. The theorems are about a single-peak MMR with forward-fold bagging. No QMDB operation
  root is in their scope. For one peak the two policies fold to the same digest, so only the
  domain byte differs.
- Recommendation. Give the client QMDB's domain byte and build the test trees with
  `qmdb::hasher()`. The proofs do not depend on the byte: probe `R6` sets it to 1 and every proof
  module still builds, which the README already notes for the domain bytes. Until then, describe
  the target as single-peak MMR inclusion with forward-fold bagging.

### F2

**"The extracted production verifier" is a second verifier written for the proof.**
Overclaim, L7 and L2.

- Claim. The report's result row says "two openings that the extracted production verifier
  accepts". The theorems are named `production_binding_or_collision`, `production_unique` and so
  on, and their comments and the `Snapshot` comment say "the production verifier".
- Evidence. The statements are about `qmdb.verify`, extracted from
  `verification/symbolic/src/qmdb.rs`. Production never calls it. Production's verifier is
  `Proof::verify_element_inclusion`, whose outer function `reconstruct_root_inner` is not
  extracted. The two share `traversal::reconstruct` and the encodings of `terms.rs`. The report
  does say so further down, under "Extracted scope" and "Outside the proof".
- Also. The byte-level sentence says "at one location under one root". The statement checks both
  openings against one trusted height `h` as well. The sentence about traces does mention the
  trusted height.
- Impact. A reader of the results table takes binding as proved for production's verifier. It is
  proved for a verifier that runs production's traversal and encodings on one item of a tree with
  one peak, and tests on trees of up to 64 leaves tie the two together (see F1 and F4 for what
  those tests leave out).
- Recommendation. Write "the extracted verifier of the verification-only client, which runs
  production's traversal and hash-input encodings", and name the trusted height in the first
  sentence. Rename the `production_` theorems or reword their comments.

### F3

**Nothing shows that the client ever logs an event.** Weak evidence, L6.

- Claim. The trace theorems speak of "every opening that the extracted client logs on a
  reachable trace". The report's pictures say that the step returns an acceptance "which the
  client logs".
- Evidence. Probe `L8` changes the QMDB `client` so that it never logs, and probe `L9` does the
  same to the shared `accept`. With the proof scripts of the two changed definitions adapted,
  every module builds: the security theorems, the sanity checks and the axiom audit, and for
  `L9` also the leaf and BLS libraries. `attempt_reachable` proves that the trace of an attempt
  is reachable, not that it holds an event. `accepts_alice` is about the value that the Rust
  step returns.
- Cause. DyLean's Hoare triples are partial: an action that fails satisfies every postcondition.
  So a mistake in `receive`, `accept` or `client` that makes the client fail would make the trace
  theorems hold for the empty reason, and no check would notice.
- Recommendation. Add one theorem to `SanityChecks.lean`: some reachable trace logs the `Opened`
  event of Alice's honest opening. It needs execution lemmas for `sendMessage`, `receiveMessage`
  and `logEvent`; DyLean exports only their partial triples.

### F4

**The proof fields that the attacker writes are never varied, and no statement covers them.**
Weak evidence, L2.

- Evidence. Production reads the tree size `leaves` and `inactive_peaks` from the proof and
  relies on the root committing to them. The client takes a trusted `height` and fixes the
  inactive count at 0. `verifiers_agree_with_production` always passes `leaves: proof.leaves`
  and `inactive_peaks: 0`, and always gives the client the true height.
- Probes. `probe_proof_fields` gives production 45,085 honest openings whose proof claims
  another size or inactive count: it accepts none. `probe_wrong_height` gives the client 1,270
  honest openings at another height: it accepts none. `probe_other_sizes` confirms the scope:
  of 1,953 honest openings of trees whose size is not a power of two, production accepts all
  and the client accepts none.
- Impact. Production behaves as intended on what was tried. The property that makes an
  attacker-chosen size harmless, that the root commits to it, is outside every theorem.
- Recommendation. Keep the three probes as tests. A statement in which the size comes from the
  proof and only the root is trusted would close the gap.

### F5

**Production's byte hashing is read, not tested or extracted.** Weak evidence, L4.

- Evidence. The byte-level theorems instantiate the hash with `ByteHash.scheme`, a handwritten
  account of `ByteTerms` in `storage/src/merkle/hasher.rs`. `ByteTerms` is not extracted. The
  tests run the client over the test-only `Concrete`. They could not run it over `ByteTerms`:
  the crate includes `terms.rs` by path, so its `Terms` trait is a different trait from the one
  that `ByteTerms` implements. That the hash is of the concatenated parts rests on the comments
  of `Hasher::hash` in `hasher.rs` and in `commonware_cryptography`.
- One difference. `ByteTerms::hash` panics when given more than `MAX_PARTS` parts, and the
  Lean reading is total. Every caller in `terms.rs` passes at most four, which is `MAX_PARTS`.
- Recommendation. Accept as a ten-line review item, or extract `ByteTerms::hash` over an
  abstract byte hasher so that the reading becomes a checked lemma.

### F6

**Production does not build every digest from `terms.rs`.** Overclaim, L0 and L5.

- Claim. `verification/qmdb/README.md`: "Production builds every Merkle digest from
  `hasher/terms.rs`".
- Evidence. `Standard::node_digest_pair` in `hasher.rs` lists the parts `[position, left,
  right]` itself and calls `H::hash_pair`. The tree builder calls it at two places in
  `storage/src/merkle/batch.rs`. Hashers that override the default methods, such as the grafting
  hasher, also bypass `terms.rs`; the README names that case.
- Impact. Honest roots, which the snapshot assumption is about, are built through an encoding
  that the proof does not see. That it agrees with `terms::node_digest` is shown by the unit
  test `test_node_digest_pair_matches_node_digest` on one pair of nodes and by
  `production_openings_verify` on 511 openings.
- Recommendation. Express `node_digest_pair` through a part list shared with `terms.rs`, or
  correct the sentence.

### F7

**The toolchain cannot be rebuilt from the repository.** Process, L8 and A1.

- The hax binary is `.verification-tools/qmdb/qmdb-hax-tools/target/release/cargo-hax`. On this
  machine it was built from a clone of `github.com/pereq-dev/hax` at `0d2f66ed6` with one
  locally modified file. `toolchain.sh` names the path only: no URL, revision or hash.
- The Aeneas Lean library comes from the fork `pereq-dev/aeneas` at the tag `build-2b9e3ea`.
  The manifest pins its commit, and the checked-out packages match the manifest (checked for
  aeneas, hax and mathlib).
- The extraction's `.lake/packages` is a link into another worktree.
- DyLean at its pin targets Lean 4.36.0-rc1. It is built here with Lean 4.35.0 and the patch.
- No CI job runs `check.sh`.
- Recommendation. Record the hax URL and revision in `toolchain.sh` and build the binary from
  them; run `check.sh` in CI.

### F8

**The axiom audit covers two namespaces, and `sorry` elsewhere is only a warning.** Process, L8.

- Evidence. `#audit_axioms Qmdb Commonware.Symbolic` audits the theorems whose names start with
  those prefixes, and follows their proofs wherever they lead (probes `A2` and `A4`). Probe `A6`
  plants `theorem Elsewhere.planted_sorry … := sorry`: the build passes with the warning
  ``declaration uses `sorry` ``. `check.sh` does not look for that warning.
- Impact. None today: every statement that the report cites is in an audited namespace, and a
  theorem outside them cannot be cited without the audit following it.
- Recommendation. Make `check.sh` fail on a `sorry` warning in the build log.

### F9

**The patch to DyLean adds a definition that the statements depend on.** Note, L6 and A3.

- Evidence. The first hunk of `lean435.patch` adds an ordering on byte arrays with its
  lawfulness instances, which DyLean's literal terms need and Lean 4.35 lacks. The closure probe
  finds `DY.Literal.Literal.instOrdByteArray_dY` among the definitions that the symbolic and
  trace statements mention. The other two hunks change an error message and the registration of
  a trace class.
- Impact. The ordering is a definition with proved laws, not an axiom, so it cannot make a false
  statement provable. It is part of what "DyLean's core" means on this toolchain.
- Status. Accepted. It goes away when the extraction moves to the Lean that DyLean targets.

### F10

**The header of `qmdb/README.md` is stale.** Process, L7.

- It names the worktree `.worktrees/qmdb-hax-dylean`, which no longer exists, and the source
  revision `0d3bf4a23`.

## Checks that passed

| Check | Link | Evidence |
| --- | --- | --- |
| Each sentence of the report's Merkle row maps to a statement with those hypotheses, apart from the wording in F2 | L7 | the claim table of the guide; read statement by statement |
| The statements depend on the handwritten definitions that the guide shows, and on no others | L7, L4, L6 | `Closure.lean`. The byte-level statements reach `Scheme`, `Scheme.terms`, `ByteHash`, `ByteHash.scheme` and nine definitions of `Verifier.lean`, and nothing of DyLean. The trace statements add `part`, `chain`, `hashing`, `messages`, `toSlice`, `toByteArray`, `Snapshot`, `Opened`, `client`, `accept`, `receive` and the three `#combine` results. The event invariant and the proof-side `#combine` blocks are in no statement |
| The refactor preserves behaviour | L0 | read the diff of `hasher.rs` and `proof.rs`: each encoding passes the same parts in the same order, and the two root branches became one test on the same value. `general_traversal_matches_reference` compares the old and new traversal for both families and both bagging policies on every range of trees with 1 to 16 leaves. `RangePlan::new` rejects a size above `MAX_LEAVES`, so `start + width` cannot overflow where production calls the traversal |
| The proof sees the files that production compiles | L1 | `lib.rs` includes `terms.rs` and `traversal.rs` by `#[path]`; neither file has a `use` |
| The boundaries of the client and the traversal are pinned by the proofs | L2, L8 | 13 of 15 probes `R1` to `R15` break `Qmdb.Verifier` or `Qmdb.Symbolic`: both bounds, the height limit, the cursor, the positions of leaf, node and peak, the range, the size in the root, the child order, the element source and the logged location. `R6` (domain byte) and `R10` (collected digests) survive, as the README says |
| The trusted Lean is pinned where a statement or a sanity check can pin it | L4, L5, L6 | probes `L1` to `L7` each break a module: digest equality, the symbolic concatenation, the byte reading, the message reading, the client's root, the snapshot assumption and the reachable steps. `L7` is caught by the sanity checks only |
| The axiom audit notices escape hatches | L8, A2 | probes `A1` to `A5`: `sorry` in a new theorem, `sorry` deep in `leaf_eq` (reported for all seven security theorems), an axiom in the namespace, an axiom elsewhere that a theorem uses, and `native_decide` |
| The report's numbers | L8 | a clean `check.sh` at `2d9ac6d2d` exits 0: 126 theorems on standard axioms, 3 Rust tests, 1,653 claims (printed by a temporary line) and 511 honest openings (the sum of `2^h` for heights 0 to 8), 3 `#guard` checks, 7 mutations of which 5 are in production files |
| The generated Lean is reproducible and nothing was added by hand | A1 | `check.sh` regenerates and compares; `build.py` fails if `Assumptions/FunsExternal.lean` declares anything |
| The patch applies to DyLean at its pin, and the checkout is clean at the pin | A3 | `check.sh` asserts both |
