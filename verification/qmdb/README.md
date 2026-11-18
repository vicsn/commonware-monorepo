# QMDB inclusion with DyLean

- Approach / branch / worktree: DyLean, `verify/qmdb-hax-dylean`, `.worktrees/qmdb-hax-dylean`.
- Status: complete for single-item symbolic client authentication, with the specification
  written in Rust and extracted with hax.
- Updated: 2026-11-18. Source: `88e372068`; production traversal pinned at `5b7e44f63`.
- Proved scope: every acceptance on a reachable trace names the trusted snapshot height, an
  in-range location and the stored item. The client's decision is the extracted Rust
  `client_step`; it runs the pinned production traversal.
- Last validation: `bash verification/qmdb/dylean/check.sh` on 2026-11-18 at `88e372068`,
  passed. 4 Rust tests (differential against this branch's production verifier and root),
  reproducible extraction, 16 theorem dependency audits (standard Lean axioms), 6 executed
  client decisions and 5 rejected Rust-source mutations. Logs: `dylean/.lake/logs/`.
- Remaining boundary: concrete hashing (SHA-256 appears only in tests), production callbacks
  outside the traversal, multiple peaks and multi-item ranges, the journal and storage.
- Next step: none required for this scope. Optional: hax contracts on the spec, BLS routing.

## Specification in Rust

The trusted specification is the Rust crate in [dylean/rust](dylean/rust/src). It is generic
over [`Terms`](dylean/rust/src/terms.rs): literals, items, digests, parsing, concatenation and
hashing. Tests instantiate it with byte strings and SHA-256. Lean instantiates the extraction
with DyLean's symbolic constructors. [spec.rs](dylean/rust/src/spec.rs) defines the digest
encodings, the honest tree and root, replay in left-first order and `verify_single`.
[client.rs](dylean/rust/src/client.rs) defines the `Acceptance` event and `client_step`.
[adapter.rs](dylean/rust/src/adapter.rs) runs the pinned production
`traversal::reconstruct` with callbacks over the same terms. The crate has no production
dependency and changes no production file.

[tests.rs](dylean/rust/src/tests.rs) builds MMRs with this branch's `commonware-storage`
(base `b45ef2d78`) for heights 0 to 8. The spec's root equals the production root. The
specification, the pinned traversal and `Proof::verify_element_inclusion` agree on 1,653
honest, substituted, misplaced, reordered, short, long, wrong-item and wrong-root claims at
heights 0 to 6. These tests sample production behaviour; they do not extend the theorem to
SHA-256.

## What Lean proves

[DyTerms](dylean/DyTerms.lean) is the trusted glue: the `Terms` instance with DyLean
constructors, the application-supplied `Snapshot` and its `Store`. The previous handwritten
[model](dylean/Model.lean) and [binding proofs](dylean/Binding.lean) are unchanged and now serve
as an untrusted reference with [Reference](dylean/Reference.lean). [Correspondence](dylean/Correspondence.lean)
proves that the extraction, interpreted with `dyTerms`, equals that reference: the honest tree,
replay with any sibling slice, `verify_single`, the production traversal through the adapter,
the root and `client_step`.

[Protocol](dylean/Protocol.lean) is trusted. Its `client` receives a message and logs exactly
the event that the extracted `client_step` returns. `client_eq_reference` makes it equal to an
executable client with the reference decision. The event invariant and the Hoare triple give
[authentication on reachable traces](dylean/SecurityTheorems.lean). The same module proves that
the production traversal and the Rust specification accept the same openings. Root
authenticity is an input.

[Scenarios](dylean/Scenarios.lean) executes the client decision on honest, substituted,
misplaced, short and long openings. [SanityChecks](dylean/SanityChecks.lean) proves the
corresponding send/client traces reachable. The interpreter cannot load DyLean and Aeneas
together (both register `trace.Step`), so the scenarios run the reference decision, which
`client_step_eq` equates with the extracted one.
[mutations.py](dylean/mutations.py) re-extracts the crate after dropping the item from leaf
hashing, changing the root's family domain, misrouting the midpoint, ignoring unused siblings or
skipping the client's verification; each breaks `Correspondence`.

## Review boundary, dependencies and generated files

Review the Rust crate (`terms.rs`, `spec.rs`, `client.rs`, `adapter.rs`), `DyTerms.lean`, the
client, invariant, `#combine` configuration and statements in `Protocol.lean`, the statements
in `SecurityTheorems.lean`, the [compatibility patch](dylean/lean435.patch) and the tool pins.
Lean checks the rest. hax/Charon/Aeneas translation, CoreModels, DyLean and Lean's kernel are
trusted.

`dylean/rust/proofs/lean/QmdbDylean/Extraction/` is generated from the crate and the pinned
traversal by the managed hax CLI (Aeneas `build-2b9e3ea`, Charon `nightly-2026.10.31`, Lean
4.35.0, `hax-lean v0.3.42`). It needs no opaque assumptions. The
[bridge runner](dylean/check-bridge.sh) archives the traversal into ignored `.lake/`, runs the
Rust tests, regenerates the extraction and fails unless it is byte-identical to the committed
files, builds the patched DyLean pin `2254f7d19` under Lean 4.35.0 and checks every module.
Keep the DyLean checkout beside the canonical monorepo (override with `DYLEAN`). Local
`.lake/packages` symlinks reuse the hax Lean experiment's dependency builds and are optional.
