# SAKE handshake with DyLean

- Approach / branch: DyLean, `verify/qmdb-hax-dylean`.
- Status: authentication in both directions, key confirmation, injective agreement and secrecy
  of the transcript are proved on DyLean traces over the extracted production steps, for SAKE
  V1. Time, V0 and the record protocol are [not covered](#what-is-not-proved).
- Updated: 2026-11-23. Source: `7b9c5b7f7`. The production files
  `cryptography/src/handshake/sake/{rules.rs,protocol.rs,mod.rs}` are as in `75e42e942`.
- Proved scope: on every trace that an attacker can reach who controls the network and the
  schedule and can compromise any identity key and what any peer keeps between its steps,
  - a dialer that finishes a handshake with a listener finishes an exchange that this listener
    answered earlier with the same secret transcript; the exchange names the namespace, both
    identity keys, both timestamps and both ephemeral keys;
  - a listener that finishes a handshake with a dialer finishes an exchange that this dialer
    finished earlier with this listener and the same secret transcript, so replaying a `Syn`
    does not by itself get a listener to finish;
  - no event of a peer matches two finishes: an answer of a listener matches one finish of a
    dialer, and a finish of a dialer matches one finish of a listener;
  - the attacker does not know the secret transcript of a finished handshake.

  Each holds unless the identity key of the peer was compromised before the handshake finished.
  The listener's statement and secrecy also fail when what either peer keeps for the exchange
  is compromised: the dialer's ephemeral secret or the listener's secret transcript. Secrecy
  survives a compromise of the identity keys after the handshake finished. On the extracted
  steps alone, honest runs complete with the same secret transcript on both sides, and a dialer
  rejects a `SynAck` that carries the listener's signature of another transcript. The steps
  are the extracted Rust that production runs. No reference model is involved.
- Assumptions: signatures, hashing, Diffie-Hellman and message authentication codes are
  symbolic constructors. A signature verifies only for the message it signs, a hash fixes its
  input, nothing but the two ephemeral secrets gives the shared secret, and only someone who
  knows a key computes a code under it. Each peer knows the identity key of the peer it names,
  as an application's peer set provides.
- Last validation: `bash verification/check.sh` on 2026-11-23 at `7b9c5b7f7`, passed.
  Reproducible extraction, a Lean build with no warnings, an axiom audit of all 159 theorems in
  `Sake` and `Commonware.Symbolic` (standard Lean axioms) and 9 rejected mutations. The
  production files were validated at `75e42e942`: `just test` for `commonware-cryptography`
  (838 passed), `commonware-stream` (39 passed) and `commonware-p2p` (493 passed), the
  conformance tests of `cryptography` and `stream` with no fixture regenerated, clippy,
  `just check-stability`, the no-std tests and the WASM build of `cryptography`. Logs:
  `verification/.lake/logs/`.
- Remaining boundary: the production instance in `protocol.rs` (BLAKE3 transcripts and their
  framing, X25519, the identity signature scheme, zeroization), `Context::new`, the wire codec,
  the stream wrapper with its cleartext prelude, bouncer and clock, and the record protocol.
- Next step: a reachable trace on which both peers finish.

SAKE is one target of the shared symbolic verification in [verification/](../README.md): one
extracted crate, one Lean package and one check for every target. This README covers what SAKE
adds.

## The handshake

`D` and `L` are the identity keys of the dialer and the listener, `X` and `Y` their ephemeral
public keys and `N` the transcript after the namespaces. `‖` commits a packet.

| Message | Fields | Signed or derived from |
| --- | --- | --- |
| D → L `Syn` | `t_D`, `X`, `sig_D` | `sig_D` signs `N‖t_D‖L‖D‖X` |
| L → D `SynAck` | `t_L`, `Y`, `sig_L`, `c_l2d` | `sig_L` signs `N‖t_D‖L‖D‖X‖t_L‖Y`; the secret transcript `T` appends the shared secret; `c_l2d` confirms `T` |
| D → L `Ack` | `c_d2l` | confirms `T` under the dialer's label |

This is V1, which both p2p networks configure. V0 commits `D` after `sig_D`.

## Production Rust

Production runs every step through
[`sake/rules.rs`](../../cryptography/src/handshake/sake/rules.rs), which has no imports. It
states the four steps over four traits:

- `Terms`: commit a timestamp or an ephemeral key to a transcript, derive an ephemeral public
  key, commit the secret that an ephemeral secret shares with a peer's key, derive a confirmation
  for a label and compare two confirmations.
- `Identity`: the local identity commits itself to a transcript and signs it.
- `Peer`: the peer's identity is committed to a transcript, and its signature of one is checked.
- `Fresh`: an ephemeral secret that is drawn when it is first needed, so the listener draws its
  key only after the dialer's signature verifies, as before.

`dial_start`, `listen_start`, `dial_end` and `listen_end` fix what each peer commits, signs and
checks, and in which order. A flag selects where the dialer's identity is committed, so one code
path serves V0 and V1. The steps read no clock and draw no randomness: the clock value, the
window of accepted timestamps and the `Fresh` secret are arguments.

[`sake/protocol.rs`](../../cryptography/src/handshake/sake/protocol.rs) keeps every public type
and signature. It instantiates `Terms` with BLAKE3 transcripts and X25519, `Identity` with any
`Signer`, `Peer` with any `PublicKey` and `Fresh` with any `CryptoRng`, and each public step
calls its rule and maps a `Rejection` to the existing `Error`. Messages on the wire are
unchanged: the conformance fixtures of `cryptography` (`SakeV0`, `SakeV1`, every message byte
and the final summary for 4096 seeds each) and of `stream` pass without regeneration.

Four tests were added before the refactor and pass on both sides of it, for both versions: a
timestamp at each end of the window and just outside it, a dialer that expects another listener,
a `SynAck` signed by another identity than the expected listener, and a correctly signed `Syn`
or `SynAck` whose ephemeral key makes the exchange non-contributory. None of these rejections
had a test.

## Extracted Rust

The shared crate in [verification/symbolic](../symbolic/src) includes `rules.rs` unchanged
through `#[path]` as its module `sake`. SAKE adds no module of its own: the Lean actions call
the extracted production steps directly. Both versions are extracted; the theorems fix the flag
to V1.

## The model

[Terms](../lean/Sake/Terms.lean) reads the extracted traits in DyLean and is trusted.

| Rust | DyLean term |
| --- | --- |
| a transcript | everything committed to it, concatenated in order onto `start ns`, a hash of the namespace |
| a timestamp | the literal of its eight big-endian bytes |
| `Identity` | commits `Signature.vk key`; signs the hash of the transcript with DyLean's signature, whose nonce the action draws |
| `Peer` | commits the peer's key; `Signature.verify` on the hash of the transcript |
| `public`, `exchange` | `DiffieHellman.dhPk`; commits `DiffieHellman.dh peer secret` and never rejects |
| `confirmation` | `Mac.mac`, the message authentication code of the label under the hash of the transcript |
| `same`, `Fresh` | equality of terms; a secret drawn before the step runs |

`start ns` stands for `Context::new`, which is not extracted. Production computes a confirmation
with BLAKE3 keyed by the transcript's summary, which is a code of the label under that summary.

DyLean has theories for hashing, signatures and key derivation and none for a keyed value that
carries a claim, so [Mac](../lean/Commonware/Symbolic/Mac.lean) adds one, in the form of
DyLean's own theories. Its trusted part is small: a code is a free constructor of a key and a
message, the attacker obtains one only by computing it from a key and a message that it knows,
and a code is checked by computing it again. Its checked part says that a code is as public as
its message, and that a valid code satisfies the predicate a protocol attaches to its codes
unless the attacker knows the key.

[Protocol](../lean/Sake/Protocol.lean) is trusted too. It has four actions, `dial`, `listen`,
`finishDial` and `finishListen`. Each looks up identity keys in DyLean's public-key
infrastructure, draws its randomness, runs one extracted step with the shared `run`, logs an
event, stores what the step keeps and sends the message that the step returns.

The attacker chooses who dials whom, every namespace, clock value and window, the claimed dialer
of a `Syn` and the timestamps of received messages. Timestamps are public, so they are inputs of
the receiving action and not fields of the term on the network. The attacker can register and
compromise identity keys. It can also compromise what a peer keeps between its steps, at any
time: `compromiseDialer` reveals a dialer's ephemeral secret and `compromiseListener` a
listener's secret transcript. What a peer keeps is stored twice, as the record its next step
reads and as this secret part; the rest of the record is public.

A finishing action stops when the finish it would log is already on the trace (`firstTime`).
This is the one part of an action that is not a step of the extracted Rust. It stands for
production's ownership: `dial_end` and `listen_end` take what the peer kept by value, so a peer
finishes from it at most once.

Two things still give the attacker more traces than production does: a dialer may finish two
different answers from one kept opening, and what a peer kept can be compromised after it
finished, when production has erased it.

## What Lean proves

[Steps](../lean/Sake/Steps.lean) states what each extracted step computes on these terms:

- `dial_start_eq`, `listen_start_eq`, `dial_end_eq` and `listen_end_eq`: the checks of each step
  in order, with the rejection each failed check returns, and the transcripts, signatures and
  confirmations that the step returns when it accepts.
- `Opening.signed_inj` and `Exchange.signed_inj`: a signed transcript fixes the namespace, the
  identity keys, the timestamps and the ephemeral keys it was built from.
- `Opening.signed_ne`: no transcript is signed both by a dialer and by a listener. DyLean has no
  lemma that different constructors give different terms, so the two are told apart by length.
- `label_ne`: the two confirmations are codes of different messages.

[Proof](../lean/Sake/Proof.lean) defines the invariant and proves that every action preserves
it.

- Signatures. An identity key signs only the opening of a dialer that logged its start, or the
  exchange of a listener that logged its answer with the secret transcript its ephemeral key
  gives. A peer that verifies a signature therefore finds the matching event of the key's owner
  on the trace, unless the key is compromised. For the dialer, `DiffieHellman.dh_commutes`
  shows that the listener's secret transcript is its own.
- Secrecy. The signature also says that the signed ephemeral key belongs to a secret that only
  a compromise of what its owner keeps reveals. The shared secret, and with it the transcript,
  is then known only to whoever compromises what one of the two peers keeps
  (`agreed_secrecy`).
- Confirmations. The dialer's confirmation is computed only by a dialer that has logged that it
  finished the exchange with that transcript. A listener that checks it finds that event, unless
  the attacker knows the transcript (`Mac.mac_checked`). The listener's confirmation carries no
  claim: its signature already binds it, and `label_ne` keeps the attacker from sending it back
  as the dialer's.
- Names. An identity key has one owner: `owner_unique` in [Owner](../lean/Sake/Owner.lean),
  from the label that DyLean's public-key infrastructure gives a key. So the dialer that
  finished is the one the listener looked up (`starter_unique`), and the listener that a dialer
  names when it finishes is the owner of the key it verified.
- Finishing once. A finish is logged only if it is not on the trace yet, so the same finish is
  never logged at two times (`dial_finish_once`, `listen_finish_once`).

[The statements](../lean/Sake/SecurityTheorems.lean), with the sentence of the `Handshake`
contract in `stream/src/lib.rs` that each backs:

| Statement | Says | Contract |
| --- | --- | --- |
| `handshake_completes` | when each timestamp is inside the other peer's window, the four extracted steps accept each other's messages and both peers end with the same secret transcript | "returns the same transcript `T` to both peers" |
| `foreign_signature_rejected` | `dial_end` rejects a `SynAck` that carries the listener's signature of another transcript | a sanity check |
| `dialer_authentication` | a logged `dialFinish dialer listener exchange secret` has `listenStart listener exchange secret` logged earlier, or the listener's identity key compromised earlier | "A dial to `peer` succeeds only if `L` is `peer`"; properties 1 and 3 for the dialer |
| `listener_authentication` | a logged `listenFinish listener dialer exchange secret` has `dialStart dialer exchange.toOpening` logged earlier, or the dialer's identity key compromised earlier | "returns `D`"; property 1. Rests on the signature alone, so a replayed `Syn` satisfies it |
| `listener_key_confirmation` | a logged `listenFinish listener dialer exchange secret` has `dialFinish dialer listener exchange secret` logged earlier, or the dialer's identity key or what either peer keeps for the exchange compromised earlier | property 3 for the listener: "Each peer returns `T` only after verifying that the other peer holds `T`" |
| `dialer_injective_agreement` | two logged `dialFinish` that are matched by one logged `listenStart` are the same finish, logged at the same time | with `dialer_authentication`: each finish of a dialer has an answer of its listener that no other finish shares |
| `listener_injective_agreement` | two logged `listenFinish` that are matched by one logged `dialFinish` are the same finish, logged at the same time | with `listener_key_confirmation`: each finish of a listener has a finish of its dialer that no other finish shares |
| `dialer_secrecy` | the attacker knows the `secret` of a logged `dialFinish` only if the listener's identity key was compromised before it, or what either peer keeps for the exchange is compromised at some time | property 2: "unpredictable to any party other than `D` and `L`" |
| `listener_secrecy` | the same for a logged `listenFinish` and the dialer's identity key | property 2 |

None of the trace statements excludes a compromise of the local identity key: a dialer whose own
key is compromised still authenticates its listener.

[Audit](../lean/Sake/Audit.lean) checks that every theorem in `Sake` and `Commonware.Symbolic`
depends only on Lean's standard axioms.

[mutations.toml](mutations.toml), run by [mutate.py](../mutate.py), re-extracts the crate after
skipping the dialer's signature check in the listener or the listener's in the dialer, signing
before the dialer commits its identity, swapping the two identities in the listener's
transcript, signing before the listener commits its ephemeral key, skipping either confirmation
check, accepting the timestamp at the end of the window, or deriving both confirmations with the
listener's label. Each breaks `Sake.Steps`, where the lemma that states what the step computes
no longer holds; Lake does not go on to the modules after it.

Five further probes were run by hand on 2026-11-23 and are not part of `check.sh`. The first
four mutate the Rust and restate the step lemma for the mutated step, so that `Sake.Steps`
builds and the question is whether the proofs after it still do.

| Probe | Result |
| --- | --- |
| The dialer skips the listener's signature | `Sake.Proof` fails in `finishDial.proof`, where the verified signature is used |
| The listener skips the dialer's signature | `Sake.Proof` fails in `listen.proof`, where the verified signature is used |
| The listener accepts any confirmation | `Sake.Proof` fails in `finishListen.proof`, where the checked confirmation is used |
| Both confirmations use the listener's label, in `dial_end` and in `listen_end` | `Sake.Proof` fails in `finishListen.proof` at `label_ne`: the attacker could send the listener's confirmation back as the dialer's |
| The dialer ignores whether the exchange is contributory | Survives: every proof builds, because the model's exchange never rejects. `test_non_contributory_exchange_fails` covers the check in production |

## What is not proved

| Gap | Why | What it needs |
| --- | --- | --- |
| That a reachable trace has both peers finish. `handshake_completes` covers the steps, not the actions around them, so the trace statements would also hold if an action could never finish. | A trace-level run needs the handles of six actions. | A statement like `Qmdb.Completeness`. |
| V0, and the key substitution it admits. | DyLean's signature is ideal: a signature verifies under one key. | DyLean's ACME example has a signature without exclusive ownership; with it the substitution should appear as a trace. |
| Non-contributory exchanges. | Symbolic Diffie-Hellman has no low-order points, so `Rejection::Ephemeral` is never returned in the model. | Outside the symbolic model; the production test covers the rejection. |
| Time. Timestamps are attacker-chosen numbers and no statement speaks about the window. | The clock is outside the steps. | A model of clocks and synchrony. |
| The record protocol and its keys. | DyLean has no theory of authenticated encryption. | An AEAD theory; the secret transcript is the key material it would start from. |

## Review boundary

Review the shared boundary listed in [verification/](../README.md) once. SAKE adds `rules.rs`,
the definitions in `Terms.lean` (`stamp`, `start`, `sakeTerms`, `Signer`, `signer`, `peer`,
`fresh`, `Opening`, `Exchange`), the constructor and attacker rule in `Mac.lean` (`Mac.SubF`,
`mac`, `mac.attackerKnowledge`), the events, kept states and their secret parts, messages,
actions, the check `firstTime`, compromise predicates and `#combine` configuration in
`Protocol.lean`, and the statements in `SecurityTheorems.lean`. Lean checks the proofs, the
invariant in `Proof.lean` and the invariants of `Mac.lean` included. `Owner.lean` is checked
too; it opens DyLean's definitions with `import all` to compute the label of a key. The production instance in `protocol.rs` is outside
the extraction and covered by production's own tests and conformance fixtures.
