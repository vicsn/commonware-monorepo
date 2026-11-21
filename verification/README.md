# Symbolic verification with hax and DyLean

Rust that production runs is extracted to Lean with hax and proved secure in DyLean's symbolic
model. One crate, one extraction and one Lean package serve every target. A target adds a Rust
module, a directory of Lean modules and a mutation table, and reuses the shared reading of
terms and clients.

| Target | Rust | Lean | Report |
| --- | --- | --- | --- |
| Leaf commitment, the smallest target | [symbolic/src/leaf.rs](symbolic/src/leaf.rs) over production `terms.rs` | [lean/Leaf](lean/Leaf) | [leaf/README.md](leaf/README.md) |
| QMDB single-item inclusion | [symbolic/src/qmdb.rs](symbolic/src/qmdb.rs) over production `terms.rs` and `traversal.rs` | [lean/Qmdb](lean/Qmdb) | [qmdb/README.md](qmdb/README.md) |
| BLS certificates | [symbolic/src/bls.rs](symbolic/src/bls.rs) over production `rules.rs` | [lean/Bls](lean/Bls) | [bls/README.md](bls/README.md) |

## Layout

- [toolchain.sh](toolchain.sh): the pins (Lean 4.35.0, DyLean `2254f7d19`, the managed hax CLI)
  and the shared setup: one DyLean build in `.lake/dylean`, patched by
  [lean435.patch](lean435.patch), and optional reuse of dependency builds.
- [check.sh](check.sh): checks every target. Logs go to `.lake/logs`.
- [mutate.py](mutate.py): re-extracts mutated Rust and requires the named proof modules to fail.
  Each target lists its mutations in a table: [leaf/mutations.toml](leaf/mutations.toml),
  [qmdb/mutations.toml](qmdb/mutations.toml) and [bls/mutations.toml](bls/mutations.toml).
- [symbolic/](symbolic): the crate that hax extracts, outside the Commonware workspace.
  - `lib.rs` includes production modules unchanged through `#[path]`:
    `storage/src/merkle/hasher/terms.rs`, `storage/src/merkle/proof/traversal.rs` and
    `cryptography/src/bls12381/certificate/rules.rs`.
  - [client.rs](symbolic/src/client.rs): what every client shares.
  - One module per target, [qmdb.rs](symbolic/src/qmdb.rs) and [bls.rs](symbolic/src/bls.rs),
    with differential tests against production.
  - [concrete.rs](symbolic/src/concrete.rs): SHA-256 and BLS12-381 instances for those tests.
  - `proofs/lean/CommonwareSymbolic/`: the generated extraction.
- [lean/](lean): the Lean package, on Lean's module system.
  - `Commonware/Symbolic/`: the glue that every target shares (below).
  - One directory per target, `Qmdb/` and `Bls/`, ending in an `Audit` module.

## Terms

Production owns the seam. `terms::Terms` hashes a list of `Part`s, each raw bytes or a digest,
and `hasher/terms.rs` lists the parts of every default Merkle hash input (`leaf_digest`,
`node_digest`, `fold`, `root`). Production instantiates it with `ByteTerms`, which concatenates
the bytes and hashes them. Lean reads the extracted trait in two ways:

- [Hashing](lean/Commonware/Symbolic/Hashing.lean): a `Scheme` is any hash with an encoding of
  parts into one message. `ByteHash.scheme` is production's reading over byte strings, for
  statements that hold up to an explicit collision.
- [Terms](lean/Commonware/Symbolic/Terms.lean): `hashing` reads byte parts as DyLean literals,
  concatenates parts to the right and applies any hash on terms, which may collide. `symbolic` is
  that reading with DyLean's hash constructor. The checked lemmas show that the reading keeps
  parts apart and that DyLean's hash has no collisions.

`Terms` is generic over DyLean's term algebra: it applies to any target whose `#combine`
includes literals, concatenation and hashing. A target that needs more constructors, such as
signatures or Diffie-Hellman, adds them to its own `#combine`. `#combine +toplevel` declares
global instances, so modules of targets with different algebras cannot be imported together;
each target is its own library.

## Signatures

Production owns this seam too. `rules::Terms` adds keys, hashes a namespace and message to a
point and checks a signature, and `rules.rs` states the certificate checks over it and over a
`Committee`, `Signers` and a `Decoded` signature. Production instantiates it with BLS12-381
hashing and the pairing check. Lean reads the extracted traits in two ways:

- [Signing](lean/Commonware/Symbolic/Signing.lean): a `Signing` is any key addition, hash and
  check. `Roster` and `Flags` read a committee and its signer flags as lists, and `decoded`
  reads a signature as an optional point. Statements about what the rules accept hold for
  every `Signing`.
- [Linear](lean/Commonware/Symbolic/Linear.lean): keys are integer combinations of member
  secrets and signatures are integer combinations of hashed inputs, under any hash, which may
  collide. `Derives` is what an attacker obtains from signing and compromise by adding and
  scaling, which covers recombination, rogue keys and keys that sum to zero. The checked
  `attribution` reduces a signature that verifies to a signing event of a protected member or
  to a collision, the alternative that `Hashing` defines for every target.

The linear model lives outside DyLean's term algebra: a target that uses it needs only literals
in its `#combine` and states what the attacker may submit as the precondition of its client's
transition.

## Clients

A client step is a pure Rust function. It takes the client's trusted state, a received message
and adversary-chosen parameters, and returns the event to log or `None`. It performs no I/O.
[client::Messages](symbolic/src/client.rs) reads the item that a received message carries;
`Commonware.Symbolic.messages` reads it as a DyLean literal.

[Client](lean/Commonware/Symbolic/Client.lean) runs an extracted step in DyLean. `accept step`
runs a step whose inputs are already fixed and logs the event it accepts, or fails. `receive
step handle` first receives the message at `handle` from the network. `accept_preserves` and
`receive_preserves` reduce preservation of the trace invariant to the event invariant of every
accepted event. A target supplies the step, its event type, its `#combine` configuration and its
`ProtocolEvent.EventInv` instance, which is its security policy. Steps that keep state, send
messages or draw nonces are not supported yet; add them to `client.rs` and `Client.lean` with
the first target that needs them.

## Adding a target

1. Add `symbolic/src/<target>.rs` with the client step and differential tests against
   production. Include any further production module through `#[path]` in `lib.rs`.
2. Run `check.sh` once and commit the regenerated extraction.
3. Add `lean/<Target>/`: an `Assumptions` module with the `#combine` of its term algebra and the
   inputs that the application supplies, the proofs, a `Protocol` module with `receive` or
   `accept`, the
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

## Report

[hax-dylean.html](hax-dylean.html) records what is proved, assumed and validated for every
target. Its links open files of the checkout that holds it.
`python3 verification/qmdb/dylean-pictures.py` regenerates its pictures from the statements that
Lean prints. `python3 verification/qmdb/report-artifact.py --out <file>` writes a copy for
publishing, whose links open GitHub at a pushed revision. The report links to the audit guide, so
pass `--page hax-dylean-audit.html=<URL>` with the place where the guide is published.

## Audit

[hax-dylean-audit.html](hax-dylean-audit.html) is a step plan for auditing the Merkle target. It
states what the audit assumes, the hax pipeline first, and shows side by side the code that must
agree: production and the verification-only client, Rust and its generated Lean, Rust traits and
their handwritten Lean readings, sentences of the report and theorem statements.

- [audit/guide.html](audit/guide.html) and [audit/pairs.toml](audit/pairs.toml): the prose and
  the table of panels, whose items are addressed by name. `python3 verification/audit/build.py`
  writes the page, and `check.sh` fails when it is stale.
- [audit/FINDINGS.md](audit/FINDINGS.md): a first pass through the guide.
- [audit/probes.py](audit/probes.py) with [audit/probes.toml](audit/probes.toml): the mutations
  of that pass with their recorded verdicts. Some survive. [audit/probes/](audit/probes) holds
  its differential tests and the script that lists what the statements depend on.
- Publish the guide like the report: `python3 verification/qmdb/report-artifact.py --report
  verification/hax-dylean-audit.html --page hax-dylean.html=<URL> --out <file>`.

## Shared review boundary

Review once for all targets: the production modules that the crate includes, `client.rs`,
`Hashing.lean`, the definitions in `Terms.lean` (`part`, `chain`, `symbolic`, `messages`), in
`Signing.lean` and in `Linear.lean`, `accept` and `receive` in `Client.lean`, `Audit.lean`, the
compatibility patch and the tool pins. Lean checks the rest, including the lemmas in
`Terms.lean` and `Linear.lean`, `accept_preserves`, `receive_preserves` and `RustM.lean`. The
hax/Charon/Aeneas translation, CoreModels, DyLean and Lean's kernel are trusted. Each target's
README lists what it adds.
