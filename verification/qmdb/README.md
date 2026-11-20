# QMDB inclusion with DyLean

- Approach / branch / worktree: DyLean, `verify/qmdb-hax-dylean`, `.worktrees/qmdb-hax-dylean`.
- Status: complete for single-item position binding of the extracted production verifier under
  any hash, and for symbolic client authentication on top of it.
- Updated: 2026-11-20. Source: `3378277a5`. It changes the production files
  `storage/src/merkle/{hasher.rs,hasher/terms.rs,proof.rs,proof/traversal.rs}`.
- Proved scope: for any hash, two openings that the production verifier accepts at one location
  under one root carry the same item, or an explicit finder returns two different hash inputs
  with the same digest. This holds for production's concatenated bytes with fixed-length digests.
  The verifier never panics or diverges, accepts every honest opening and rejects one with an
  unused sibling. With DyLean's collision-free hash, every acceptance on a reachable trace names
  the trusted snapshot height, an in-range location and the stored item. The client's decision is
  the extracted Rust `client_step`. No reference model is involved.
- Assumption: the application's snapshot root gives every stored item an opening that the
  production verifier accepts. `honest_snapshots_exist` shows that such roots exist at every
  height up to 62.
- Last validation: `bash verification/check.sh` on 2026-11-20 at `3378277a5`, passed. 3 Rust
  tests (1,653 differential claims and 511 honest production openings), reproducible extraction,
  an axiom audit of all 109 theorems in `Qmdb` and `Commonware.Symbolic` (standard Lean axioms),
  2 executed finder checks, 7 rejected mutations and the BLS check. The production files are
  unchanged since `just test -p commonware-storage` passed on 2026-11-18 (4,672 passed, 994
  skipped). Logs: `verification/.lake/logs/`, with the earlier runs in
  `verification/.lake/logs/1976be622/`.
- Remaining boundary: the hash function itself and production's `ByteTerms`, which Lean reads as
  hashing the concatenated bytes; the production `Hasher`/`Family` wrappers, their bounds checks
  and blueprint; hashers that override the default encodings (grafting); node collection;
  multiple peaks and multi-item ranges; the journal and storage.
- Next step: extend the client to the production blueprint (several peaks, range proofs,
  collection), or prove that accepted openings are unique.

QMDB is one target of the shared symbolic verification in [verification/](../README.md): one
extracted crate, one Lean package and one check for every target. This README covers what QMDB
adds.

## Production Rust

Production builds every Merkle digest from [`hasher/terms.rs`](../../storage/src/merkle/hasher/terms.rs):
`leaf_digest`, `node_digest`, `fold` and `root` list the parts of each hash input (raw bytes or
digests) and pass them to a `Terms` implementation. The default `Hasher` methods hash the
concatenated bytes through `ByteTerms`, so production digests are unchanged. Proof verification
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
extraction with DyLean's symbolic constructors.

[qmdb/tests.rs](../symbolic/src/qmdb/tests.rs) builds MMRs with this branch's
`commonware-storage`. Every production opening at heights 0 to 8 verifies under the production
root. The client and `Proof::verify_element_inclusion` agree on 1,653 honest, substituted,
misplaced, reordered, short, long, wrong-item and wrong-root claims at heights 0 to 6. These tests
sample production behaviour; they do not extend the theorems to SHA-256.

## What Lean proves

The shared glue in [lean/Commonware/Symbolic](../lean/Commonware/Symbolic) states what a hash, a
term and a client are to the extracted code (see [verification/](../README.md)):
[Hashing](../lean/Commonware/Symbolic/Hashing.lean) reads the extracted `Terms` for any hash
`Scheme` and for production's `ByteHash.scheme`; [Terms](../lean/Commonware/Symbolic/Terms.lean)
reads it symbolically (`symbolic`: byte parts as literals, right-nested concatenation, DyLean's
hash constructor) and reads messages as literals (`messages`), and proves the reading injective
and collision-free for any DyLean algebra with these constructors;
[Client](../lean/Commonware/Symbolic/Client.lean) runs an extracted step as a DyLean action.

[Verifier](../lean/Qmdb/Verifier.lean) states `Unambiguous`: an encoding that keeps leaf, node and
root inputs apart. It proves the following for every scheme, by induction over the extracted
`traversal::reconstruct`:

- `binding_or_collision`: two openings that `verify` accepts at one location under one root carry
  the same item, or `finder` returns a collision. The finder lists the hash inputs that each
  opening builds, from the root's down to the leaf's, and returns the first corresponding pair
  that differs and has one digest. It is a computable function, at most `height + 2` pairs long.
  The encoding must be unambiguous.
- `byte_binding_or_collision`: the same for `ByteHash.scheme`, whose encoding Lean proves
  unambiguous, so the collision is between two byte strings.
- `verify_total`: `verify` returns a verdict on every input, so adversarial siblings cannot make
  it panic or diverge.
- `honest_opening` and `extra_sibling_rejected`: on an honest snapshot the honest siblings are
  accepted, and the same siblings followed by an unused one are rejected.

[Assumptions](../lean/Qmdb/Assumptions.lean) is trusted: QMDB's term algebra (`#combine` of
literals, concatenation and hashing) and the application-supplied `Snapshot` with its root and
honest-opening assumption. [Symbolic](../lean/Qmdb/Symbolic.lean) proves that the symbolic scheme
is unambiguous, so with the shared no-collision lemma the verifier is binding (`binding`). From
that, `client_step_sound`, `honest_accepted` and `substitution_rejected`: an accepted message names
the snapshot height, an in-range location and the stored item; honest messages are accepted; any
other item at a location is rejected whatever the siblings.

[Protocol](../lean/Qmdb/Protocol.lean) is trusted. Its `client` is the shared `receive` action over
the extracted `client_step`: it receives a message and logs exactly the event that `client_step`
returns. The shared `receive_preserves` reduces the Hoare triple to `client_step_sound`, and the
event invariant gives [authentication on reachable traces](../lean/Qmdb/SecurityTheorems.lean).
Root authenticity is an input. [SanityChecks](../lean/Qmdb/SanityChecks.lean) instantiates a
two-item snapshot, proves the extracted client's decisions on honest, substituted, misplaced and
long openings, and proves the send/client traces reachable. It also takes a hash with a single
digest: `finder_finds` proves that the finder returns a collision for two snapshots that differ at
a location, and an executed check shows the pair it returns for `Alice` and `Bob`, their two leaf
inputs. [Audit](../lean/Qmdb/Audit.lean) checks that every theorem in `Qmdb` and
`Commonware.Symbolic` depends only on Lean's standard axioms.

[mutations.toml](mutations.toml), run by [mutate.py](../mutate.py), re-extracts the crate after
dropping the element from leaf hashing, the left child from node hashing or the peak from the
root, making the traversal treat a subtree that ends at the queried location as inside or hash
the right child twice, or ignoring unused siblings; each breaks `Qmdb.Verifier`. Skipping the
client's verification breaks `Qmdb.Symbolic`. The proofs do not fix the family domain bytes, so
changing them is caught by the Rust tests only. Swapping the child digests passed to node
collection survives: the client collects nothing.

## Review boundary, dependencies and generated files

Review the shared boundary listed in [verification/](../README.md) once: `terms.rs`,
`traversal.rs`, `client.rs`, `Hashing.lean`, the definitions in `Terms.lean`, `receive` in
`Client.lean`, `Audit.lean`, the [compatibility patch](../lean435.patch) and the tool pins. QMDB
adds `qmdb.rs`, `Assumptions.lean`, `Unambiguous`, the statements and the `finder` in
`Verifier.lean`, the client, invariant, `#combine` configuration and statements in
`Protocol.lean`, and the statements in `SecurityTheorems.lean`. Lean checks the proofs.
hax/Charon/Aeneas translation, CoreModels, DyLean and Lean's kernel are trusted.

`verification/symbolic/proofs/lean/CommonwareSymbolic/Extraction/` is generated from the shared
crate and the production files it includes by the managed hax CLI (Aeneas `build-2b9e3ea`,
Charon `nightly-2026.10.31`, Lean 4.35.0, `hax-lean v0.3.42`). It needs no opaque assumptions.
[check.sh](../check.sh) runs the Rust tests, regenerates the extraction and fails unless it is
byte-identical to the committed files, builds the patched DyLean pin `2254f7d19` under Lean 4.35.0
once for every target, builds every Lean module (including the executed checks and the axiom
audit), runs the mutations and checks the BLS target. Keep the DyLean checkout beside the
canonical monorepo (override with `DYLEAN`). Local `.lake/packages` symlinks reuse the hax Lean
experiment's dependency builds and are optional. After one run, `verification/lean` is a Lake
package that an editor can open with Lean 4.35.0.
