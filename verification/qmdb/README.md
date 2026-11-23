# QMDB inclusion with DyLean

- Approach / branch: DyLean, `verify/qmdb-hax-dylean`.
- Status: complete for uniqueness of the single-item openings that the extracted verifier accepts
  under DyLean's ideal hash, and for client authentication on top of it.
- Updated: 2026-11-22. It changes the production files
  `storage/src/merkle/{hasher.rs,hasher/terms.rs,proof.rs,proof/traversal.rs}`.
- Proved scope: the hash is DyLean's hash constructor, so a root is one term that fixes every
  digest below it. Two openings that the extracted verifier accepts at one location under one
  root, for one trusted height, carry the same item and the same siblings. The verifier never
  panics or diverges, accepts every honest opening and rejects one with an unused sibling. Every
  acceptance logged on a reachable trace names the trusted snapshot height, an in-range location
  and the item stored there. The client's decision is the extracted Rust `client_step`. No
  reference model is involved.
- Assumption: the application's snapshot supplies a root and, for every stored item, the siblings
  of an opening that the extracted verifier accepts under it. `honest_snapshots_exist` shows
  that such roots and siblings exist at every height up to `MAX_HEIGHT`, the client's limit,
  which is production's `MAX_LEAVES` as a height.
- Last validation: `bash verification/check.sh` on 2026-11-22, passed. 3 Rust tests (1,653
  differential claims and 511 honest production openings), reproducible extraction, an axiom
  audit of all 98 theorems in `Qmdb` and `Commonware.Symbolic` (standard Lean axioms) and 7
  rejected mutations. The production files are unchanged since `just test -p commonware-storage`
  passed on 2026-11-18 (4,672 passed, 994 skipped). Logs: `verification/.lake/logs/`.
- Remaining boundary: the hash function itself, which the model treats as ideal, and production's
  `ByteTerms`; the production `Hasher`/`Family` wrappers, their bounds checks and blueprint;
  hashers that override the default encodings (grafting); node collection; multiple peaks and
  multi-item ranges; the journal and storage.
- Next step: extend the client to the production blueprint (several peaks, range proofs,
  collection).

QMDB is one target of the shared symbolic verification in [verification/](../README.md): one
extracted crate, one Lean package and one check for every target. This README covers what QMDB
adds. An [audit guide](../hax-dylean-audit.html) walks through this target, and
[audit/FINDINGS.md](../audit/FINDINGS.md) records a first pass through it.

## Production Rust

The default `Hasher` methods build their digests from
[`hasher/terms.rs`](../../storage/src/merkle/hasher/terms.rs): `leaf_digest`, `node_digest`,
`fold` and `root` list the parts of each hash input (raw bytes or digests) and pass them to a
`Terms` implementation. They hash the concatenated bytes through `ByteTerms`, so production
digests are unchanged. `Standard::node_digest_pair`, which the tree builder calls, lists the
parts of a node input itself; a unit test compares it with `node_digest`. Proof verification
runs [`proof/traversal.rs`](../../storage/src/merkle/proof/traversal.rs): `reconstruct` and its
`Opening` backend, which reads elements and siblings in left-first order and hashes through a
`Nodes` implementation. `proof.rs` supplies `FamilyNodes`, which forwards to the `Hasher` and the
family's child positions, so a hasher that overrides `node_digest` (grafting) keeps working.

## Extracted Rust

The shared crate in [verification/symbolic](../symbolic/src) includes `terms.rs` and
`traversal.rs` unchanged through `#[path]`. [client.rs](../symbolic/src/client.rs), shared by
every client, defines `Messages`, which reads the item that a received message carries. QMDB adds
only [qmdb.rs](../symbolic/src/qmdb.rs): MMR child positions and a `Nodes` implementation over the
production encodings, a single-element source, `verify` (height and location bounds, the
production traversal over one peak, sibling exhaustion, the production root encoding with
forward-fold bagging) and `client_step`, which parses a message and returns the `Acceptance` event
when `verify` accepts it under the trusted root. Tests instantiate `Terms` and `Messages` with the
shared SHA-256 instances in [concrete.rs](../symbolic/src/concrete.rs); Lean instantiates the
extraction with DyLean terms and DyLean's hash constructor.

[qmdb/tests.rs](../symbolic/src/qmdb/tests.rs) builds MMRs with this branch's
`commonware-storage`. Every production opening at heights 0 to 8 verifies under the production
root. The client and `Proof::verify_element_inclusion` agree on 1,653 honest, substituted,
misplaced, reordered, short, long, wrong-item and wrong-root claims at heights 0 to 6. These tests
sample production behaviour; they do not extend the theorems to SHA-256.

## What Lean proves

The shared glue in [lean/Commonware/Symbolic](../lean/Commonware/Symbolic) states what a hash, a
term and a client are to the extracted code (see [verification/](../README.md)).
[Terms](../lean/Commonware/Symbolic/Terms.lean) reads the extracted `Terms` on DyLean terms
(`dyTerms`: byte parts as literals, right-nested concatenation, DyLean's hash constructor, digests
compared as terms) and reads messages as literals (`messages`). It proves that the reading keeps
parts apart, for any DyLean algebra with these constructors.
[Client](../lean/Commonware/Symbolic/Client.lean) runs an extracted step as a DyLean action.

[Assumptions](../lean/Qmdb/Assumptions.lean) is trusted: QMDB's term algebra (`#combine` of
literals, concatenation and hashing) and the application-supplied `Snapshot` with its root, the
siblings of every stored item and their honest-opening assumption.

[Verifier](../lean/Qmdb/Verifier.lean) proves the following by induction over the extracted
`traversal::reconstruct`:

- `unique`: two openings that `verify` accepts at one location under one root carry the same item
  and the same siblings. A digest is a term. A leaf digest fixes its item, a node digest its two
  children and a root its peak (`leafTerm_inj`, `nodeTerm_inj`, `rootTerm_inj`), so equal roots
  force equal terms all the way down to the leaf. `verify` leaves no sibling unread, so the
  sibling lists agree too. Position binding is the item half.
- `maxHeight` and `maxLeaves`: the extracted `MAX_HEIGHT` and the leaves of a tree of that
  height. Every statement and proof names them, and `maxHeight_eq` states the value once.
- `verify_total` and `verify_bounds`: `verify` returns a verdict on every input, so adversarial
  siblings cannot make it panic or diverge, and it accepts only heights up to `maxHeight` and
  locations inside the tree.
- `honest_opening` and `extra_sibling_rejected`: on an honest snapshot the honest siblings are
  accepted, and the same siblings followed by an unused one are rejected.

[Symbolic](../lean/Qmdb/Symbolic.lean) proves `client_step_sound`: a message that the extracted
client step accepts names the snapshot height and an in-range location, and its item is the
stored one, because the snapshot has an accepted opening there and accepted openings are unique.
From that, `honest_accepted` and `substitution_rejected`: honest messages are accepted; any other
item at a location is rejected whatever the siblings.

[Protocol](../lean/Qmdb/Protocol.lean) is trusted. Its `client` is the shared `receive` action over
the extracted `client_step`: it receives a message and logs the acceptance that `client_step`
returns. The shared `receive_preserves` reduces the Hoare triple to `client_step_sound`.
[SecurityTheorems](../lean/Qmdb/SecurityTheorems.lean) states the two results about the protocol
and its assumption. `client_authentication`: an acceptance logged on a reachable trace names the
snapshot height, an in-range location and the item stored there. `honest_snapshots_exist`: the
snapshot assumption can be met. Root authenticity is an input. No theorem is stated twice: the
verifier's properties are cited from `Verifier.lean`.
[SanityChecks](../lean/Qmdb/SanityChecks.lean) instantiates a two-item snapshot, proves the
extracted client's decisions on honest, substituted, misplaced and long openings, and proves the
send/client traces reachable. [Audit](../lean/Qmdb/Audit.lean) checks that every theorem in `Qmdb`
and `Commonware.Symbolic` depends only on Lean's standard axioms.

[mutations.toml](mutations.toml), run by [mutate.py](../mutate.py), re-extracts the crate after
dropping the element from leaf hashing, the left child from node hashing or the peak from the
root, making the traversal treat a subtree that ends at the queried location as inside or hash
the right child twice, or ignoring unused siblings; each breaks `Qmdb.Verifier`. Skipping the
client's verification breaks `Qmdb.Symbolic`. The proofs do not fix the family domain bytes, so
changing them is caught by the Rust tests only. Swapping the child digests passed to node
collection survives: the client collects nothing.

## Review boundary, dependencies and generated files

Review the shared boundary listed in [verification/](../README.md) once: `terms.rs`,
`traversal.rs`, `client.rs`, the definitions in `Terms.lean`, `receive` in `Client.lean`,
`Audit.lean`, the [compatibility patch](../lean435.patch) and the tool pins. QMDB adds `qmdb.rs`,
`Assumptions.lean`, `maxHeight` and the statements of `unique`, `verify_total`, `verify_bounds`,
`honest_opening` and `extra_sibling_rejected` in `Verifier.lean`, the client, invariant and `#combine` configuration
in `Protocol.lean`, and the statements in `SecurityTheorems.lean`. Lean checks the proofs.
hax/Charon/Aeneas translation, CoreModels, DyLean and Lean's kernel are trusted.

`verification/symbolic/proofs/lean/CommonwareSymbolic/Extraction/` is generated from the shared
crate and the production files it includes by the managed hax CLI (Aeneas `build-2b9e3ea`,
Charon `nightly-2026.10.31`, Lean 4.35.0, `hax-lean v0.3.42`). It needs no opaque assumptions.
[check.sh](../check.sh) runs the Rust tests, regenerates the extraction and fails unless it is
byte-identical to the committed files, builds the patched DyLean pin `2254f7d19` under Lean 4.35.0
once for every target, builds every Lean module (including the executed checks and the axiom
audit) and runs the mutations of every target. Keep the DyLean checkout beside the
canonical monorepo (override with `DYLEAN`). Local `.lake/packages` symlinks reuse the hax Lean
experiment's dependency builds and are optional. After one run, `verification/lean` is a Lake
package that an editor can open with Lean 4.35.0.
