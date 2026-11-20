# Symbolic verification with hax and DyLean

Rust that production runs is extracted to Lean with hax and proved secure in DyLean's symbolic
model. One crate, one extraction and one Lean package serve every target. A target adds a Rust
module, a directory of Lean modules and a mutation table, and reuses the shared reading of
terms and clients.

| Target | Rust | Lean | Report |
| --- | --- | --- | --- |
| QMDB single-item inclusion | [symbolic/src/qmdb.rs](symbolic/src/qmdb.rs) over production `terms.rs` and `traversal.rs` | [lean/Qmdb](lean/Qmdb) | [qmdb/README.md](qmdb/README.md) |
| BLS signer attribution | the hax Lean experiment's extraction at `d1a5e7ca3` | [bls/Protocol.lean](bls/Protocol.lean) | [bls/README.md](bls/README.md) |

BLS does not use the shared crate or Lean package yet; its check shares the toolchain and the
DyLean build.

## Layout

- [toolchain.sh](toolchain.sh): the pins (Lean 4.35.0, DyLean `2254f7d19`, the managed hax CLI)
  and the shared setup: one DyLean build in `.lake/dylean`, patched by
  [lean435.patch](lean435.patch), and optional reuse of dependency builds.
- [check.sh](check.sh): checks every target. Logs go to `.lake/logs`.
- [mutate.py](mutate.py): re-extracts mutated Rust and requires a named proof module to fail.
  Each target lists its mutations in a table, such as [qmdb/mutations.toml](qmdb/mutations.toml).
- [symbolic/](symbolic): the crate that hax extracts, outside the Commonware workspace.
  - `lib.rs` includes production modules unchanged through `#[path]`:
    `storage/src/merkle/hasher/terms.rs` and `storage/src/merkle/proof/traversal.rs`.
  - [client.rs](symbolic/src/client.rs): what every client shares.
  - One module per target, such as [qmdb.rs](symbolic/src/qmdb.rs), with differential tests
    against production.
  - [concrete.rs](symbolic/src/concrete.rs): SHA-256 instances for those tests.
  - `proofs/lean/CommonwareSymbolic/`: the generated extraction.
- [lean/](lean): the Lean package, on Lean's module system.
  - `Commonware/Symbolic/`: the glue that every target shares (below).
  - One directory per target, such as `Qmdb/`, ending in an `Audit` module.

## Terms

Production owns the seam. `terms::Terms` hashes a list of `Part`s, each raw bytes or a digest,
and `hasher/terms.rs` lists the parts of every default Merkle hash input (`leaf_digest`,
`node_digest`, `fold`, `root`). Production instantiates it with `ByteTerms`, which concatenates
the bytes and hashes them. Lean reads the extracted trait in two ways:

- [Hashing](lean/Commonware/Symbolic/Hashing.lean): a `Scheme` is any hash with an encoding of
  parts into one message. `ByteHash.scheme` is production's reading over byte strings, for
  statements that hold up to an explicit collision.
- [Terms](lean/Commonware/Symbolic/Terms.lean): `symbolic` reads byte parts as DyLean literals,
  concatenates parts to the right and applies DyLean's hash constructor. The checked lemmas show
  that this reading keeps parts apart and has no collisions.

`Terms` is generic over DyLean's term algebra: it applies to any target whose `#combine`
includes literals, concatenation and hashing. A target that needs more constructors, such as
signatures or Diffie-Hellman, adds them to its own `#combine`. `#combine +toplevel` declares
global instances, so modules of targets with different algebras cannot be imported together;
each target is its own library.

## Clients

A client step is a pure Rust function. It takes the client's trusted state, a received message
and adversary-chosen parameters, and returns the event to log or `None`. It performs no I/O.
[client::Messages](symbolic/src/client.rs) reads the item that a received message carries;
`Commonware.Symbolic.messages` reads it as a DyLean literal.

[Client](lean/Commonware/Symbolic/Client.lean) runs an extracted step in DyLean. `receive step
handle` receives the message at `handle`, runs `step` and logs the event it accepts, or fails.
`receive_preserves` reduces preservation of the trace invariant to the event invariant of every
accepted event. A target supplies the step, its event type, its `#combine` configuration and its
`ProtocolEvent.EventInv` instance, which is its security policy. Steps that keep state, send
messages or draw nonces are not supported yet; add them to `client.rs` and `Client.lean` with
the first target that needs them.

## Adding a target

1. Add `symbolic/src/<target>.rs` with the client step and differential tests against
   production. Include any further production module through `#[path]` in `lib.rs`.
2. Run `check.sh` once and commit the regenerated extraction.
3. Add `lean/<Target>/`: an `Assumptions` module with the `#combine` of its term algebra and the
   inputs that the application supplies, the proofs, a `Protocol` module with `receive`, the
   event invariant and the theorem statements, and an `Audit` module that runs
   `#audit_axioms` over the target's namespace. Add a `lean_lib` to
   [lakefile.toml](lean/lakefile.toml).
4. Add `<target>/mutations.toml` and run it from `check.sh`.

## Running

```bash
bash verification/check.sh
```

Keep the DyLean checkout beside the canonical monorepo at the pin (override with `DYLEAN`), the
managed hax CLI in `.verification-tools/qmdb/qmdb-hax-tools` (override with `HAX`), and Lean
4.35.0 in elan. Dependency builds are reused from the hax Lean experiment's worktree when it is
present; otherwise Lake builds them. After one run, `lean/` is a Lake package that an editor can
open.

## Shared review boundary

Review once for all targets: the production modules that the crate includes, `client.rs`,
`Hashing.lean`, the definitions in `Terms.lean` (`part`, `chain`, `symbolic`, `messages`),
`receive` in `Client.lean`, `Audit.lean`, the compatibility patch and the tool pins. Lean checks
the rest, including the lemmas in `Terms.lean`, `receive_preserves` and `RustM.lean`. The
hax/Charon/Aeneas translation, CoreModels, DyLean and Lean's kernel are trusted. Each target's
README lists what it adds.
