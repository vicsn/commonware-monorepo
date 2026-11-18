# QMDB inclusion with DyLean

- Approach / branch / worktree: DyLean, `verify/qmdb-hax-dylean`, `.worktrees/qmdb-hax-dylean`.
- Status: complete for single-item symbolic client authentication and traversal correspondence.
- Updated and validated: 2026-11-18, proof source `9310a34cf`, extracted Rust source `5b7e44f63`.
- Reproduce from the worktree: `bash verification/qmdb/dylean/check.sh`.
- Results: seven theorem dependency audits (standard Lean axioms), six reachable
  network/client scenarios and three rejected mutations. The ordinary report baseline is `b45ef2d78`.
- Remaining boundary: production callbacks, concrete hashing, the outer verifier and journal.

The [protocol](dylean/Protocol.lean) follows DyLean's Merkle example. It combines
literal, concatenation and hash attacker-knowledge rules, network sends, client
steps and acceptance events. A client reads a network handle, checks an opening
at the supplied location under a fixed snapshot root and logs acceptance on
success. The caller can supply arbitrary sibling terms. The event invariant
and the action's Hoare triple imply [authentication on reachable traces](dylean/SecurityTheorems.lean):
every accepted event has the trusted height, an in-range location and the item
stored there. Root authenticity is an input to this experiment.

[Correspondence](dylean/Correspondence.lean) instantiates the hax-extracted
refactored Rust traversal with DyLean hash constructors, MMR geometry and a
list of siblings. Replay agrees with [the model](dylean/Model.lean) on digest,
unused suffix and missing-sibling failure. The top-level symbolic checker bounds
height and location, checks exhaustion and wraps the root. This wrapper and
backend are handwritten; the Rust extraction covers the traversal. DyLean hash
injectivity and structural concatenation are symbolic laws. [Binding](dylean/Binding.lean)
also proves honest-opening existence, stored-item inclusion and fixed-root binding.

[Sanity checks](dylean/SanityChecks.lean) prove the send/check scenarios reachable
and execute the model checker on honest, substituted, misplaced, short and long
openings. Verifier equality transfers these scenarios to the extracted checker.
Dropping the item bytes, misrouting the midpoint or bypassing the client's
verification guard fails the corresponding unchanged proof.

## Dependencies and generated files

Keep the pinned DyLean checkout beside the canonical monorepo (override with
`DYLEAN`), plus the hax experiment toolchain and Lean dependencies. The
[bridge runner](dylean/check-bridge.sh) archives exact source revisions into
ignored `.lake/` paths, regenerates the Lean extraction with the managed hax
CLI, compares generated definitions with their pinned versions, and builds them.
The standalone model checks on DyLean's Lean 4.36.0-rc1. The combined check uses
Lean 4.35.0 and a [compatibility patch](dylean/lean435.patch) on the archived
DyLean copy for byte-array ordering laws and a tactic diagnostic. Review the
patch, handwritten modules, tool pins, and upstream constructor theories.
The extraction and Lean object files are regenerated outputs. Compiler and
translation correctness remain trusted. Detailed bridge and mutation diagnostics
are in `dylean/.lake/bridge/`.
