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

| | Leaf | QMDB inclusion | BLS certificates |
| --- | --- | --- | --- |
| Production code extracted | one function | hash-input encodings, traversal and its opening backend | the certificate rules |
| Production files changed | none beyond QMDB's | four | five |
| Verification-only Rust | 41 lines | 143 lines | 68 lines |
| Handwritten Lean | 206 lines | 1,442 lines | 1,192 lines |
| Hash model | DyLean's ideal hash | any hash, up to an explicit collision | any hash and signature scheme, up to an explicit collision |
| Application input | a digest and its item | a snapshot root with an accepted opening per item | the committee's registered keys |
| Trace theorem | the accepted item is the committed one | the accepted item is the stored one at an in-range location, or a collision | each protected flagged member signed strictly earlier, or a collision |
| Uses the shared crate and Lean package | yes | yes | yes |

All three go through the same extraction, the same reading of hashes and messages, the same
client action and the same axiom audit. Leaf differs from the others only in steps 2, 6, 7 and
9, and it keeps the ideal hash, so it has no collision alternative. The line counts are of the
files in `symbolic/src/<target>.rs` and `lean/<Target>/`; see each target's README for its scope.

## Checks

`bash verification/check.sh` runs the differential test, regenerates the extraction, builds the
proofs with the axiom audit and runs [mutations.toml](mutations.toml). Skipping the comparison or
hashing an empty item instead of the received one breaks `Leaf.Step`. Dropping the element from
the production leaf hash, listed in [QMDB's table](../qmdb/mutations.toml), breaks both
`Leaf.Step` and `Qmdb.Verifier`.
