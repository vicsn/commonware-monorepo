# QMDB inclusion with DyLean

- Approach / branch / worktree: DyLean, `verify/qmdb-hax-dylean`, `.worktrees/qmdb-hax-dylean`.
- Status: complete for single-item position binding of the extracted production verifier under
  any hash, and for symbolic client authentication on top of it.
- Updated: 2026-11-20. Source: `1976be622`. It changes the production files
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
- Last validation: `bash verification/qmdb/dylean/check.sh` on 2026-11-19 on the working tree
  committed as `1976be622`,
  passed. 3 Rust tests (1,653 differential claims and 511 honest production openings),
  reproducible extraction, 21 theorem dependency audits (standard Lean axioms), 2 executed finder
  checks and 7 rejected mutations. The production files are unchanged since
  `just test -p commonware-storage` passed on 2026-11-18 (4,672 passed, 994 skipped). Logs:
  `dylean/.lake/logs/`.
- Remaining boundary: the hash function itself and production's `ByteTerms`, which Lean reads as
  hashing the concatenated bytes; the production `Hasher`/`Family` wrappers, their bounds checks
  and blueprint; hashers that override the default encodings (grafting); node collection;
  multiple peaks and multi-item ranges; the journal and storage.
- Next step: extend the client to the production blueprint (several peaks, range proofs,
  collection), or prove that accepted openings are unique.

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

The crate in [dylean/rust](dylean/rust/src) includes `terms.rs` and `traversal.rs` unchanged
through `#[path]` and adds only [client.rs](dylean/rust/src/client.rs): MMR child positions and a
`Nodes` implementation over the production encodings, a single-element source, `verify` (height
and location bounds, the production traversal over one peak, sibling exhaustion, the production
root encoding with forward-fold bagging) and `client_step`, which parses a message and returns the
`Acceptance` event when `verify` accepts it under the trusted root. Tests instantiate `Terms` with
byte strings and SHA-256; Lean instantiates the extraction with DyLean's symbolic constructors.

[tests.rs](dylean/rust/src/tests.rs) builds MMRs with this branch's `commonware-storage`. Every
production opening at heights 0 to 8 verifies under the production root. The client and
`Proof::verify_element_inclusion` agree on 1,653 honest, substituted, misplaced, reordered,
short, long, wrong-item and wrong-root claims at heights 0 to 6. These tests sample production
behaviour; they do not extend the theorems to SHA-256.

## What Lean proves

[Hashing](dylean/Hashing.lean) is trusted and states what a hash is to the extracted code. A
`Scheme` is a hash function with an encoding of the parts of a hash input into one message, and
`Scheme.terms` is the `Terms` implementation that hashes the encoded parts. `Collision` is two
different messages with one digest. `Unambiguous` says that the encoding keeps inputs of one kind
apart. `ByteHash.scheme` is the production reading: the bytes of the parts are concatenated and
hashed, and digests have a fixed-length, injective byte representation.

[Verifier](dylean/Verifier.lean) proves the following for every scheme, by induction over the
extracted `traversal::reconstruct`:

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

[DyTerms](dylean/DyTerms.lean) is the trusted glue to DyLean: the `symbolic` scheme (byte parts as
literals, right-nested concatenation, DyLean's hash constructor), message parsing, and the
application-supplied `Snapshot` with its root and honest-opening assumption.
[Symbolic](dylean/Symbolic.lean) proves that this scheme is unambiguous and has no collisions, so
the verifier is binding (`binding`). From that, `client_step_sound`, `honest_accepted` and
`substitution_rejected`: an accepted message names the snapshot height, an in-range location and
the stored item; honest messages are accepted; any other item at a location is rejected whatever
the siblings.

[Protocol](dylean/Protocol.lean) is trusted. Its `client` receives a message and logs exactly the
event that the extracted `client_step` returns; the event invariant and the Hoare triple give
[authentication on reachable traces](dylean/SecurityTheorems.lean). Root authenticity is an input.
[SanityChecks](dylean/SanityChecks.lean) instantiates a two-item snapshot, proves the extracted
client's decisions on honest, substituted, misplaced and long openings, and proves the
send/client traces reachable. It also takes a hash with a single digest: `finder_finds` proves
that the finder returns a collision for two snapshots that differ at a location, and an executed
check shows the pair it returns for `Alice` and `Bob`, their two leaf inputs.

[mutations.py](dylean/mutations.py) re-extracts the crate after dropping the element from leaf
hashing, the left child from node hashing or the peak from the root, making the traversal treat a
subtree that ends at the queried location as inside or hash the right child twice, or ignoring
unused siblings; each breaks `Verifier`. Skipping the client's verification breaks `Symbolic`.
The proofs do not fix the family domain bytes, so changing them is caught by the Rust tests only.
Swapping the child digests passed to node collection survives: the client collects nothing.

## Review boundary, dependencies and generated files

Review `terms.rs`, `traversal.rs` and `client.rs`, `Hashing.lean`, `DyTerms.lean`, the client,
invariant, `#combine` configuration and statements in `Protocol.lean`, the statements and the
`finder` in `Verifier.lean`, the statements in `SecurityTheorems.lean`, the
[compatibility patch](dylean/lean435.patch) and the tool pins. Lean checks the proofs.
hax/Charon/Aeneas translation, CoreModels, DyLean and Lean's kernel are trusted.

`dylean/rust/proofs/lean/QmdbDylean/Extraction/` is generated from the crate and the production
files it includes by the managed hax CLI (Aeneas `build-2b9e3ea`, Charon `nightly-2026.10.31`,
Lean 4.35.0, `hax-lean v0.3.42`). It needs no opaque assumptions. The
[bridge runner](dylean/check-bridge.sh) runs the Rust tests, regenerates the extraction and fails
unless it is byte-identical to the committed files, builds the patched DyLean pin `2254f7d19`
under Lean 4.35.0, checks every module and audits 21 theorems for standard axioms.
[check.sh](dylean/check.sh) also checks the DyLean pin and runs the mutations. Keep the DyLean
checkout beside the canonical monorepo (override with `DYLEAN`). Local `.lake/packages` symlinks
reuse the hax Lean experiment's dependency builds and are optional. After one run, `dylean/` is a
Lake package that an editor can open with Lean 4.35.0.
