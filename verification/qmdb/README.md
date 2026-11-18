# QMDB inclusion with DyLean

- Approach / branch / worktree: DyLean, `verify/qmdb-dylean`, `.worktrees/qmdb-dylean`.
- Status: complete for the symbolic model.
- Updated and validated: 2026-11-18, source `79219519a`, production baseline `b45ef2d78`.
- Validation: from this worktree run `bash verification/qmdb/dylean/check.sh`.
  Three theorems pass the axiom audit. Two individually type-checked mutations
  (discard the claimed bytes, misroute the exact midpoint) fail the unchanged proof.
- Remaining production obligation: connect the Rust verifier, geometry, encoding,
  journal and trusted-root construction to the symbolic model.

[Model.lean](dylean/Model.lean) uses the constructor setup from DyLean's
`Examples/MerkleTree/Instance.lean`, restricted to literal, concatenation and hash.
It defines QMDB's perfect single-peak MMR geometry, positioned hashes, DFS witness
order, exact sibling consumption, and the ForwardFold root prefix for zero inactive
peaks. [Binding.lean](dylean/Binding.lean) proves that acceptance under the honest
tree root identifies the item at the query location, an honest witness exists,
and conflicting items cannot both open even an arbitrary fixed root at that location.
The proof permits arbitrary symbolic siblings. DyLean hashes are injective symbolic
constructors; concatenation preserves its component structure. These are stronger
properties than concrete hashing and byte concatenation. No computational
advantage bound or Rust refinement follows from this experiment.

The checker expects the clean [DyLean checkout](https://github.com/BobDyLean/dylean/tree/2254f7d1943acb33008e6018130aef34438dd6b2)
beside the canonical monorepo, or its path in `DYLEAN`. It checks the revision,
builds the required dependency modules with the pinned Lean version, then
runs [validate.py](dylean/validate.py). Review the model, proof, runner and
upstream constructor theories. The generated Lean objects under the two
`.lake/` directories are compiler output reproduced by the check command.
