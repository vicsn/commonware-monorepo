# Symbolic verification with hax and DyLean

Rust that production runs is extracted to Lean with hax and proved secure in DyLean's symbolic
model. One crate, one extraction and one Lean package serve every target. A target adds a Rust
module, a directory of Lean modules and a mutation table, and reuses the shared reading of
terms and clients.

| Target | Rust | Lean | Report |
| --- | --- | --- | --- |
| QMDB single-item inclusion | [symbolic/src/qmdb.rs](symbolic/src/qmdb.rs) over production `terms.rs` and `traversal.rs` | [lean/Qmdb](lean/Qmdb) | [qmdb/README.md](qmdb/README.md) |
| Ordered QMDB checkpoint reads | shared ordered claim, activity, current-root and pinned MMB verifier logic | [CheckpointAudit](lean/Qmdb/CheckpointAudit.lean) | [MMB and ordered reads](qmdb/mmb/README.md) |
| BLS certificates | [symbolic/src/bls.rs](symbolic/src/bls.rs) over production `rules.rs` | [lean/Bls](lean/Bls) | [bls/README.md](bls/README.md) |
| SAKE handshake | production `handshake/sake/rules.rs`, with no module of its own | [lean/Sake](lean/Sake) | [sake/README.md](sake/README.md) |

## Layout

- [toolchain.sh](toolchain.sh): the pins (Lean 4.35.0, DyLean `2254f7d19`, the managed hax CLI)
  and the shared setup: one DyLean build in `.lake/dylean`, patched by
  [lean435.patch](lean435.patch), and optional reuse of dependency builds.
- [check.sh](check.sh): checks every target. Logs go to `.lake/logs`.
- [mutate.py](mutate.py): re-extracts mutated Rust and requires the named proof modules to fail.
  Each target lists its mutations in a table: [qmdb/mutations.toml](qmdb/mutations.toml),
  [bls/mutations.toml](bls/mutations.toml) and [sake/mutations.toml](sake/mutations.toml).
- [symbolic/](symbolic): the crate that hax extracts, outside the Commonware workspace.
  - `lib.rs` includes production modules unchanged through `#[path]`:
    `storage/src/merkle/hasher/terms.rs`, `storage/src/merkle/proof/traversal.rs`,
    `cryptography/src/bls12381/certificate/rules.rs` and
    `cryptography/src/handshake/sake/rules.rs`.
  - [client.rs](symbolic/src/client.rs): what every client shares.
  - A module for each target whose client production does not state in full,
    [qmdb.rs](symbolic/src/qmdb.rs) and [bls.rs](symbolic/src/bls.rs), with differential tests
    against production. The steps of the SAKE handshake are production's own.
  - [concrete.rs](symbolic/src/concrete.rs): SHA-256 and BLS12-381 instances for those tests.
  - `proofs/lean/CommonwareSymbolic/`: the generated extraction.
- [lean/](lean): the Lean package, on Lean's module system.
  - `Commonware/Symbolic/`: the glue that every target shares (below).
  - One directory per target, `Qmdb/`, `Bls/` and `Sake/`, ending in an `Audit` module.

## Terms

Production owns the seam. `terms::Terms` hashes a list of `Part`s, each raw bytes or a digest,
and `hasher/terms.rs` lists the parts of every default Merkle hash input (`leaf_digest`,
`node_digest`, `fold`, `root`). Production instantiates it with `ByteTerms`, which concatenates
the bytes and hashes them. Lean reads the extracted trait once, in
[Terms](lean/Commonware/Symbolic/Terms.lean): `dyTerms` reads byte parts as DyLean literals,
concatenates parts to the right, applies DyLean's hash constructor and compares digests as terms.
The hash is ideal, as ProVerif and Tamarin treat a hash by default: two digests are equal only
when their inputs are the same term. The checked lemmas show that the reading keeps byte parts
and concatenations apart.

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
  to a collision of the hash, which `Linear` defines.

The linear model lives outside DyLean's term algebra: a target that uses it needs only literals
in its `#combine` and states what the attacker may submit as the precondition of its client's
transition.

## Handshake

Production owns this seam as well. `handshake/sake/rules.rs` states the four steps of the SAKE
handshake over `Terms` (transcripts, ephemeral keys and confirmations), `Identity` (the local
identity commits itself to a transcript and signs it), `Peer` (the peer's identity is committed
and its signature checked) and `Fresh` (an ephemeral secret that is drawn when it is first
needed). Production instantiates them with BLAKE3 transcripts, X25519, its signature schemes and
its random number generator. Lean reads them in [Sake/Terms](lean/Sake/Terms.lean) with DyLean's
signatures and Diffie-Hellman and with message authentication codes, so this target's `#combine`
adds those constructors and fresh values to literals, concatenation and hashing.

DyLean has no theory of message authentication codes.
[Mac](lean/Commonware/Symbolic/Mac.lean) adds one in the form of DyLean's own theories: a code
is a constructor of a key and a message that the attacker obtains only by computing it, and a
protocol attaches a predicate to the codes that its honest participants compute. A target that
includes it gets `Mac` as one more name for its `#combine`.

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
`ProtocolEvent.EventInv` instance, which is its security policy.

A step that keeps state, sends a message or needs randomness stays pure as well. It takes what
it kept and returns what it keeps next, it returns the message to send, and the randomness and
the clock value are arguments. `run step` returns what such a step returns, or fails. The
target's action then draws the randomness with DyLean's `Random.genRand`, stores the state with
`PersistentLocalState` and sends the message with `Network.sendMessage`. `run_returns` and
`run_ok` let a proof about the action use that the step returned its result. The SAKE handshake
is the first target of this kind.

## Adding a target

1. Add `symbolic/src/<target>.rs` with the client step and differential tests against
   production. Include any further production module through `#[path]` in `lib.rs`.
2. Run `check.sh` once and commit the regenerated extraction.
3. Add `lean/<Target>/`: an `Assumptions` module with the `#combine` of its term algebra and the
   inputs that the application supplies, the proofs, a `Protocol` module with `receive` or
   `accept` and the event invariant, a `SecurityTheorems` module with the statements, and an
   `Audit` module that runs `#audit_axioms` over the target's namespace. Add a `lean_lib` to
   [lakefile.toml](lean/lakefile.toml).
4. Add `<target>/mutations.toml` and run it from `check.sh`.

## Lean style

The handwritten Lean follows Mathlib's style where a linter checks it, and a few rules of its
own.

- Linters. [lean/lakefile.toml](lean/lakefile.toml) turns on Mathlib's style linters for every
  module: lines of at most 100 columns, spaces around operators (`2 ^ n`, not `2^n`), `·` for
  goals, `fun x => …`, one goal per tactic block, `change` where a `show` changes the goal, and
  a doc string on every public definition, field and constructor. `check.sh` fails on any
  warning of the Lean build, so it also fails on `sorry`.
- What auditors read. The statements that the report cites, and the definitions those
  statements depend on, are the trusted declarations of the audit guide's graph. Each stays
  within 80 columns, comment included, so that the guide shows it unwrapped. A signature that
  does not fit one line puts the name alone on the first line, every hypothesis and every
  assumed instance such as `[Snapshot]` on a line of its own, and the conclusion on lines of
  its own, one conjunct per line. Binders keep their order: moving one changes every caller.
  `audit/build.py` checks the width and the layout.

  ```lean
  theorem unique
      (h : Std.U32) (loc : Std.U64) (root : Bytes)
      (a b : Slice Std.U8) (wa wb : Slice Bytes)
      (ha : qmdb.verify dyTerms () h loc root a wa = RustM.ok true)
      (hb : qmdb.verify dyTerms () h loc root b wb = RustM.ok true) :
      a = b ∧
      wa = wb := by
  ```

- Names. Theorems are `snake_case`, definitions `camelCase` and types `UpperCamel`. A
  hypothesis is named for what it says (`bound`, `inside`), not numbered.
- Comments. A doc string says what holds, not how the proof goes. The comment at the top of a
  module says what in it is trusted and what is checked.
- Proofs. No `sorry`, no `native_decide` and no new axiom: the axiom audit fails the build.

Lean has no formatter, so the linters and the check are what keeps this in place.

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

[hax-dylean.html](hax-dylean.html) records what is proved, assumed and validated for the QMDB
and BLS targets; [sake/README.md](sake/README.md) is the record of the SAKE target. The report's
links open files of the checkout that holds it.
`python3 verification/qmdb/dylean-pictures.py` regenerates its pictures from the statements that
Lean prints. `python3 verification/qmdb/report-artifact.py --out <file>` writes a copy for
publishing, whose links open GitHub at a pushed revision. The report links to the audit guide:
pass `--page hax-dylean-audit.html=<URL>` if the guide is published somewhere, or the link opens
the guide's file on GitHub.

## Audit

[hax-dylean-audit.html](hax-dylean-audit.html) is a step plan for auditing the Merkle target. It
states what the audit assumes, the hax pipeline first, and shows side by side the code that must
agree: production and the verification-only client, Rust and its generated Lean, Rust traits and
their handwritten Lean readings, sentences of the report and theorem statements.

- [audit/guide.html](audit/guide.html) and [audit/pairs.toml](audit/pairs.toml): the prose and
  the table of panels, whose items are addressed by name. `python3 verification/audit/build.py`
  writes the page, and `check.sh` fails when it is stale.
- [audit/Dag.lean](audit/Dag.lean) prints every Lean declaration of the target with what it
  mentions, and [audit/dag.py](audit/dag.py) draws that as the guide's graph, coloured by trust
  type: a declaration is trusted when a statement that the report cites depends on what it says.
  After changing Lean, run `python3 verification/audit/build.py --dag` and then
  `python3 verification/audit/build.py`; `check.sh` fails when [audit/dag.json](audit/dag.json)
  is stale.
- [audit/FINDINGS.md](audit/FINDINGS.md): a first pass through the guide, and what changed since.
- [audit/probes.py](audit/probes.py) with [audit/probes.toml](audit/probes.toml): mutations of
  the Rust, of the trusted Lean and of the proofs, with their recorded verdicts. Some survive.
  [audit/probes/](audit/probes) holds differential tests that vary what the committed tests do
  not.
- Publish the guide like the report: `python3 verification/qmdb/report-artifact.py --report
  verification/hax-dylean-audit.html --out <file>`, with `--page hax-dylean.html=<URL>` if the
  report is published too.

## Shared review boundary

Review once for all targets: the production modules that the crate includes, `client.rs`,
the definitions in `Terms.lean` (`part`, `chain`, `dyTerms`, `messages`), in
`Signing.lean` and in `Linear.lean`, `accept`, `receive` and `run` in `Client.lean`,
`Audit.lean`, the compatibility patch and the tool pins. Lean checks the rest, including the
lemmas in `Terms.lean` and `Linear.lean`, `accept_preserves`, `receive_preserves`, `run_returns`,
`run_ok` and `RustM.lean`. The hax/Charon/Aeneas translation, CoreModels, DyLean and Lean's
kernel are trusted. Each target's README lists what it adds; the constructor and attacker rule
of `Mac.lean` are listed with the SAKE target, the only one that uses them.
