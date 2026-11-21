# Leaf commitment with DyLean

The smallest target, for auditing the route from production Rust to a DyLean trace theorem. It
proves a deliberately simple property and adds as little as possible to the shared setup.

- Property: a client holds a trusted digest that commits to one item. On every reachable trace,
  whatever the attacker sends, each item the client accepts is the committed item.
- Production code involved: `terms::leaf_digest` in
  [`storage/src/merkle/hasher/terms.rs`](../../storage/src/merkle/hasher/terms.rs), which the
  default production `Hasher::leaf_digest` calls. Nothing else.
- Assumption: the trusted digest is the production leaf digest of the committed item at
  position 0. `commitment_exists` shows that every item has one.
- Hash model: DyLean's collision-free hash. There is no collision reduction for this target.

## The route, step by step

| Step | File | Trusted or checked |
| --- | --- | --- |
| 1. Production function | `storage/src/merkle/hasher/terms.rs` (`leaf_digest`) | reviewed, shared |
| 2. Client step in Rust | [symbolic/src/leaf.rs](../symbolic/src/leaf.rs), 41 lines | reviewed |
| 3. Rust agrees with production | [symbolic/src/leaf/tests.rs](../symbolic/src/leaf/tests.rs) | tested with SHA-256 |
| 4. Extraction to Lean | `symbolic/proofs/lean/CommonwareSymbolic/Extraction/` | generated; hax and Aeneas are trusted |
| 5. Reading of hashes and messages | [Hashing.lean](../lean/Commonware/Symbolic/Hashing.lean), [Terms.lean](../lean/Commonware/Symbolic/Terms.lean) | trusted, shared |
| 6. Term algebra and commitment | [Leaf/Assumptions.lean](../lean/Leaf/Assumptions.lean) | trusted |
| 7. Facts about the extracted step | [Leaf/Step.lean](../lean/Leaf/Step.lean) | checked |
| 8. Client action in DyLean | `receive` in [Client.lean](../lean/Commonware/Symbolic/Client.lean) | trusted, shared |
| 9. Policy and trace theorem | [Leaf/Protocol.lean](../lean/Leaf/Protocol.lean) | statements trusted, proofs checked |
| 10. Axiom audit | [Leaf/Audit.lean](../lean/Leaf/Audit.lean) | checked by the build |

What an auditor reads for this target alone: `leaf.rs`, `Commitment` in `Assumptions.lean`, and
in `Protocol.lean` the `client`, the event invariant, the `#combine` lists and the statement of
`client_authentication`. `Step.lean` needs no review: `client_step_sound` is the only fact that
`Protocol.lean` uses, and Lean checks that it follows from the extraction and the assumption.
Steps 1, 4, 5 and 8 are the shared boundary in [verification/](../README.md), reviewed once.

`Step.lean` proves three things about the extracted step. The production leaf digest is the hash
of the position and the item. Two items with one digest are the same item, because DyLean's hash
and concatenation are injective. So the step accepts only the committed item
(`client_step_sound`), accepts it (`committed_accepted`) and rejects any other
(`other_rejected`).

## Compared with the other targets

| | Leaf | QMDB inclusion | BLS signer attribution |
| --- | --- | --- | --- |
| Production code extracted | one function | hash-input encodings, traversal and its opening backend | six verifier bodies, in the hax Lean experiment's harness |
| Production lines changed | none beyond QMDB's | four files | none |
| Verification-only Rust | 41 lines | 143 lines | a generated harness with abstract primitives |
| Handwritten Lean | 206 lines | 1,206 lines | 89 lines over an imported routing proof |
| Hash model | DyLean's ideal hash | any hash up to an explicit collision, and DyLean's for traces | not applicable; a symbolic BLS algebra |
| Application input | a digest and its item | a snapshot root with an accepted opening per item | a key registry with proofs of possession |
| Trace theorem | the accepted item is the committed one | the accepted item is the stored one at an in-range location | each protected signer signed strictly earlier |
| Uses the shared crate and Lean package | yes | yes | not yet |

Leaf and QMDB differ only in steps 2, 6, 7 and 9; everything else is the same files. BLS shares
the toolchain and the DyLean build, but its extraction and algebra come from the hax Lean
experiment.

## Checks

`bash verification/check.sh` runs the differential test, regenerates the extraction, builds the
proofs with the axiom audit and runs [mutations.toml](mutations.toml). Skipping the comparison or
hashing an empty item instead of the received one breaks `Leaf.Step`. Dropping the element from
the production leaf hash, listed in [QMDB's table](../qmdb/mutations.toml), breaks both
`Leaf.Step` and `Qmdb.Verifier`.
