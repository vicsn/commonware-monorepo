# QMDB inclusion with DyLean

- Approach / branch / worktree: DyLean, `verify/qmdb-hax-dylean`, `.worktrees/qmdb-hax-dylean`.
- Status: complete for uniqueness of the single-item openings that the extracted production
  verifier accepts under any hash, and for client authentication up to an explicit collision on
  top of it.
- Updated: 2026-11-20. Source: `0d3bf4a23`. It changes the production files
  `storage/src/merkle/{hasher.rs,hasher/terms.rs,proof.rs,proof/traversal.rs}`.
- Proved scope: for any hash, two openings that the production verifier accepts at one location
  under one root carry the same item and the same siblings, or an explicit finder returns two
  different hash inputs with the same digest. This holds for production's concatenated bytes with
  fixed-length digests. The verifier never panics or diverges, accepts every honest opening and
  rejects one with an unused sibling. For any hash on DyLean terms, every opening logged on a
  reachable trace names the trusted snapshot height and an in-range location, and its item is the
  stored one or the finder returns a collision between the logged opening and the snapshot's.
  With DyLean's collision-free hash the item is the stored one and an accepted opening is the
  only one. The client's decision is the extracted Rust `client_step`. No reference model is
  involved.
- Assumption: the application's snapshot supplies a root and, for every stored item, the siblings
  of an opening that the production verifier accepts under it. `honest_snapshots_exist` shows
  that such roots and siblings exist for every hash at every height up to 62.
- Last validation: `bash verification/check.sh` on 2026-11-20 at `0d3bf4a23`, passed. 3 Rust
  tests (1,653 differential claims and 511 honest production openings), reproducible extraction,
  an axiom audit of all 126 theorems in `Qmdb` and `Commonware.Symbolic` (standard Lean axioms),
  3 executed finder checks and 7 rejected mutations. The production files are
  unchanged since `just test -p commonware-storage` passed on 2026-11-18 (4,672 passed, 994
  skipped). Logs: `verification/.lake/logs/`, with the earlier runs in
  `verification/.lake/logs/1976be622/`.
- Remaining boundary: the hash function itself and production's `ByteTerms`, which Lean reads as
  hashing the concatenated bytes; the production `Hasher`/`Family` wrappers, their bounds checks
  and blueprint; hashers that override the default encodings (grafting); node collection;
  multiple peaks and multi-item ranges; the journal and storage.
- Next step: extend the client to the production blueprint (several peaks, range proofs,
  collection).

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
extraction with DyLean terms under any hash on them, and with DyLean's hash constructor.

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
reads it on DyLean terms (`hashing`: byte parts as literals, right-nested concatenation, any
hash on terms; `symbolic` is its instance with DyLean's hash constructor) and reads messages as
literals (`messages`), and proves the reading injective and DyLean's hash collision-free for any
DyLean algebra with these constructors;
[Client](../lean/Commonware/Symbolic/Client.lean) runs an extracted step as a DyLean action.

[Verifier](../lean/Qmdb/Verifier.lean) states `Unambiguous`: an encoding that keeps leaf, node and
root inputs apart. It proves the following for every scheme, by induction over the extracted
`traversal::reconstruct`:

- `unique_or_collision`: two openings that `verify` accepts at one location under one root carry
  the same item and the same siblings, or `finder` returns a collision. The finder lists the hash
  inputs that each opening builds, from the root's down to the leaf's, and returns the first
  corresponding pair that differs and has one digest. It is a computable function, at most
  `height + 2` pairs long. The encoding must be unambiguous. The induction carries the siblings
  that both openings have read, and `verify` leaves none unread.
- `binding_or_collision`: the item half of that statement.
- `byte_unique_or_collision` and `byte_binding_or_collision`: the same for `ByteHash.scheme`,
  whose encoding Lean proves unambiguous, so the collision is between two byte strings.
- `verify_total`: `verify` returns a verdict on every input, so adversarial siblings cannot make
  it panic or diverge.
- `honest_opening` and `extra_sibling_rejected`: on an honest snapshot the honest siblings are
  accepted, and the same siblings followed by an unused one are rejected.

[Assumptions](../lean/Qmdb/Assumptions.lean) is trusted: QMDB's term algebra (`#combine` of
literals, concatenation and hashing) and the application-supplied `Snapshot` with its hash, which
is any function on terms, its root, the siblings of every stored item and their honest-opening
assumption. [Symbolic](../lean/Qmdb/Symbolic.lean) proves that DyLean's concatenation is
unambiguous under any hash. So `client_step_sound` holds for any hash: an accepted message names
the snapshot height and an in-range location, and its item is the stored one or `finder` returns
a collision between the accepted opening and the snapshot's. With the shared no-collision lemma
for DyLean's hash, accepted openings are unique (`unique`) and the verifier is binding
(`binding`). From that, `honest_accepted` and `substitution_rejected`: honest messages are
accepted; any other item at a location is rejected whatever the siblings.

[Protocol](../lean/Qmdb/Protocol.lean) is trusted. Its `client` is the shared `receive` action over
the extracted `client_step`: it receives a message and logs the acceptance that `client_step`
returns together with the siblings it was given (`Opened`). The shared `receive_preserves`
reduces the Hoare triple to `client_step_sound`, and the event invariant gives
[authentication on reachable traces](../lean/Qmdb/SecurityTheorems.lean): a logged item is the
stored one, or `finder` returns a collision between the logged opening and the snapshot's
(`client_authentication`). With a hash that has no collisions, such as DyLean's, the item is the
stored one (`collision_free_authentication`). Root authenticity is an input. [SanityChecks](../lean/Qmdb/SanityChecks.lean) instantiates a
two-item snapshot, proves the extracted client's decisions on honest, substituted, misplaced and
long openings, and proves the send/client traces reachable. It also takes hashes that collide.
With a single digest, `finder_finds` proves that the finder returns a collision for two snapshots
that differ at a location, an executed check shows the pair it returns for `Alice` and `Bob`,
their two leaf inputs, and `flat_accepts_substituted` proves that the extracted client accepts a
substituted item, so the collision alternative cannot be dropped. With a hash that tells leaves
apart but not nodes, `finder_finds_sibling` proves that two openings of one item with different
siblings are both accepted, and an executed check shows the finder returning their node inputs. [Audit](../lean/Qmdb/Audit.lean) checks that every theorem in `Qmdb` and
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
`Verifier.lean`, the client, the logged `Opened` event, invariant, `#combine` configuration and
statements in `Protocol.lean`, and the statements in `SecurityTheorems.lean`. Lean checks the proofs.
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
