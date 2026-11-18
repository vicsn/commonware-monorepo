# QMDB inclusion with DyLean

- Approach / branch / worktree: DyLean, `verify/qmdb-hax-dylean`, `.worktrees/qmdb-hax-dylean`.
- Status: complete for single-item symbolic client authentication over the extracted production
  traversal.
- Updated: 2026-11-18. Source: `43f5af03e`; production traversal pinned at `5b7e44f63`.
- Proved scope: the production verifier is binding, and every acceptance on a reachable trace
  names the trusted snapshot height, an in-range location and the stored item. The client's
  decision is the extracted Rust `client_step`, which runs the pinned production traversal.
- Assumption: the application's snapshot root gives every stored item an opening that the
  production verifier accepts. `honest_snapshots_exist` shows that such roots exist.
- Last validation: `bash verification/qmdb/dylean/check.sh` on 2026-11-18 at `43f5af03e`,
  passed. 4 Rust tests (1,653 differential claims and 511 honest production openings), reproducible
  extraction, 15 theorem dependency audits (standard Lean axioms), 6 executed client decisions
  and 5 rejected mutations. Logs: `dylean/.lake/logs/`.
- Remaining boundary: concrete hashing (SHA-256 appears only in tests), the production adapter's
  iterator, hasher and root comparison, multiple peaks and multi-item ranges, the journal and
  storage.
- Next step: optional. Prove binding directly over the extraction instead of through the
  reference model, or extract the production adapter.

## Extracted Rust

The crate in [dylean/rust](dylean/rust/src) has no Merkle implementation of its own. It includes
the pinned production `traversal::reconstruct` and adds what the production verifier wraps
around it. [adapter.rs](dylean/rust/src/adapter.rs) supplies the traversal callbacks with the
production hasher's hash inputs (`be64` positions, leaf, node and the forward-fold root over one
peak), and `verify` checks the height and location, sibling exhaustion and the root.
[client.rs](dylean/rust/src/client.rs) parses a message and returns the `Acceptance` event when
`verify` accepts it under the trusted root. Both are generic over
[`Terms`](dylean/rust/src/terms.rs): tests instantiate it with byte strings and SHA-256, and
Lean instantiates the extraction with DyLean's symbolic constructors. No production file changes.

[tests.rs](dylean/rust/src/tests.rs) builds MMRs with this branch's `commonware-storage` (base
`b45ef2d78`). Every production opening at heights 0 to 8 verifies under the production root.
The adapter, the client and `Proof::verify_element_inclusion` agree on 1,653 honest,
substituted, misplaced, reordered, short, long, wrong-item and wrong-root claims at heights 0 to
6. These tests sample production behaviour; they do not extend the theorems to SHA-256.

## What Lean proves

[DyTerms](dylean/DyTerms.lean) is the trusted glue: the `Terms` instance with DyLean
constructors and the application-supplied `Snapshot` with its root and honest-opening
assumption. [Correspondence](dylean/Correspondence.lean) proves that the extracted traversal,
adapter and client step equal an untrusted reference built on the handwritten
[model](dylean/Model.lean) ([Reference](dylean/Reference.lean)), for every height, location and
sibling slice. With the model's [binding proofs](dylean/Binding.lean), this makes the production
verifier binding: two openings it accepts at one location under one root carry the same item.

[Protocol](dylean/Protocol.lean) is trusted. Its `client` receives a message and logs exactly
the event that the extracted `client_step` returns. `client_eq_reference` makes it equal to an
executable client with the reference decision. By binding and the snapshot assumption, an
accepted item is the stored one, so the event invariant and the Hoare triple give
[authentication on reachable traces](dylean/SecurityTheorems.lean). Root authenticity is an
input.

[Scenarios](dylean/Scenarios.lean) executes the client decision on honest, substituted,
misplaced, short and long openings, with the honest tree's root as the snapshot root.
[SanityChecks](dylean/SanityChecks.lean) proves the corresponding send/client traces reachable.
The interpreter cannot load DyLean and Aeneas together (both register `trace.Step`), so the
scenarios run the reference decision, which `client_step_eq` equates with the extracted one.
[mutations.py](dylean/mutations.py) re-extracts the crate after dropping the item from leaf
hashing, changing the root's family domain, making the production traversal treat a subtree
that ends at the queried location as inside, ignoring unused siblings or skipping the client's
verification; each breaks `Correspondence`.

## Review boundary, dependencies and generated files

Review `terms.rs`, `adapter.rs` and `client.rs`, the pinned traversal, `DyTerms.lean`, the
client, invariant, `#combine` configuration and statements in `Protocol.lean`, the statements
in `SecurityTheorems.lean`, the [compatibility patch](dylean/lean435.patch) and the tool pins.
Lean checks the rest, including the reference model. hax/Charon/Aeneas translation, CoreModels,
DyLean and Lean's kernel are trusted.

`dylean/rust/proofs/lean/QmdbDylean/Extraction/` is generated from the crate and the pinned
traversal by the managed hax CLI (Aeneas `build-2b9e3ea`, Charon `nightly-2026.10.31`, Lean
4.35.0, `hax-lean v0.3.42`). It needs no opaque assumptions. The
[bridge runner](dylean/check-bridge.sh) archives the traversal into ignored `.lake/`, runs the
Rust tests, regenerates the extraction and fails unless it is byte-identical to the committed
files, builds the patched DyLean pin `2254f7d19` under Lean 4.35.0 and checks every module.
Keep the DyLean checkout beside the canonical monorepo (override with `DYLEAN`). Local
`.lake/packages` symlinks reuse the hax Lean experiment's dependency builds and are optional.
