# BLS certificates with DyLean

- Approach / branch / worktree: DyLean, `verify/qmdb-hax-dylean`, `.worktrees/qmdb-hax-dylean`.
- Status: complete for signer-index interpretation, quorum authorization and subject and domain
  binding of multisignature certificates, at the level of the extracted production rules and on
  DyLean traces. Four further properties are assessed [below](#four-further-properties), not
  proved.
- Updated: 2026-11-20. Source: `0d3bf4a23`. It changes the production files
  `cryptography/src/bls12381/certificate/{rules.rs,mod.rs,multisig/mod.rs,threshold/mod.rs}` and
  `cryptography/src/certificate.rs`.
- Proved scope: for any signature scheme, the extracted client step returns a verdict on every
  certificate and accepts exactly when the signer flags span the committee, at least the `N3f1`
  quorum is flagged, the signature decodes, and it verifies for the hash of the given namespace
  and message under the sum of the keys registered at the flagged indices, each once and in index
  order. Two accepted certificates over one committee flag more common members than the committee
  tolerates as faulty. In the linear attacker model, for any registered keys and any hash, every
  certificate logged on a reachable trace flags a quorum, and each flagged member that registered
  its own key and was not compromised before the acceptance signed exactly that namespace and
  message strictly earlier, or the hash collides between an input that the member's secret was
  applied to and the subject or the possession input of a flagged key. The client's decision is
  the extracted Rust `client_step`. No reference model is involved.
- Assumptions: the application supplies the committee's registered keys in member order, and a
  proof of possession is derivable for every flagged key of a submitted certificate. Production
  does not check proofs of possession; registration must.
- Last validation: `bash verification/check.sh` on 2026-11-22, passed. 3 Rust tests (198
  certificate claims, 24 attestation claims and the quorum of every committee size up to
  100,000), reproducible extraction, an axiom audit of all 136 theorems in `Bls` and
  `Commonware.Symbolic` (standard Lean axioms), 3 executed checks and 10 rejected mutations. The
  count was 144 while the shared hash interface, which QMDB no longer uses, was imported. The
  production files are unchanged since `08229c65d`, where `just test -p commonware-cryptography`
  (834 passed), clippy, the no-std tests and build, the WASM build, the conformance tests and the
  consensus scheme tests passed. Logs: `verification/.lake/logs/`.
- Remaining boundary: the signature scheme itself (hashing to the curve, the pairing, group
  checks and decoding) and a computational reduction; the production adapters; signing, batch
  verification of attestations and certificate assembly; proof-of-possession checks at
  registration; the consensus wrappers that choose namespaces and subjects.
- Next step: the honest-member version of exact signer-set binding, which needs no refactor.

BLS is one target of the shared symbolic verification in [verification/](../README.md): one
extracted crate, one Lean package and one check for every target. This README covers what BLS
adds.

## Production Rust

Production checks every certificate through
[`certificate/rules.rs`](../../cryptography/src/bls12381/certificate/rules.rs), which has no
imports. It states the checks over four traits: `Terms` (the zero key, key addition, the hash of
a namespace and message, and the check of a signature), `Committee` (size, quorum and the key at
an index), `Signers` (the flags) and `Decoded` (a signature that may not decode).

- `verify_certificate`: the flags span the committee, `count` reaches the committee's quorum, the
  signature decodes, `aggregate` sums the keys at the flagged indices in index order, and one
  `check` runs on the hash of the namespace and message.
- `verify_attestation`: the key at the signer index, a decoded signature, one `check`.
- `verify_identity`: a decoded signature and one `check` under a given key, which the threshold
  scheme calls with its group key.

[`certificate/mod.rs`](../../cryptography/src/bls12381/certificate/mod.rs) holds the adapters:
`Pairing` (production hashing and the pairing check), the signer bitmap, and `Single` and
`Aggregated` for lazily decoded signatures. `multisig/mod.rs` adds `Members`, the participant map
with the quorum of the scheme's fault model. Verdicts, encodings and the public API are
unchanged. Two differences deserve review: flagged signers are counted by a loop over the bitmap,
where the previous code used its population count, and the subject's namespace and message are
computed before the length and quorum checks, where the previous code computed them after.

## Extracted Rust

The shared crate in [verification/symbolic](../symbolic/src) includes `rules.rs` unchanged
through `#[path]`. BLS adds only [bls.rs](../symbolic/src/bls.rs): `N3f1`, a committee whose
quorum is `n - (n - 1) / 3`, the `Certified` event (committee size and quorum) and `client_step`,
which rejects an empty committee and otherwise returns the event when the production rules
accept the certificate. Production asks `commonware_utils::N3f1` for the quorum, which panics on
an empty committee and on one of more than `u32::MAX` members; the client computes the same
formula over `u64`.

[bls/tests.rs](../symbolic/src/bls/tests.rs) instantiates the rules with production hashing and
pairing ([concrete.rs](../symbolic/src/concrete.rs)) and compares them with a production
multisignature scheme in both variants. The client and `Generic::verify_certificate` agree on 198
claims over committees of 1 to 13 members: honest certificates, too few signers, a bitmap of the
wrong length, another namespace or message, a signature that misses a flagged signer or includes
an unflagged one, and a signature that does not decode. The attestation rule agrees on 24 claims,
and the quorum agrees with production for every committee size up to 100,000. These tests sample
production behaviour; they do not extend the theorems to BLS12-381.

## The models

The abstractions follow One For All ([Hofmeier et al.](https://arxiv.org/abs/2505.10316)).

| Paper | Here |
| --- | --- |
| Validation models: verification is an arbitrary function, constrained by correctness and unforgeability for honest keys | [Signing](../lean/Commonware/Symbolic/Signing.lean): `hash` and `check` are any functions, and the code-level theorems hold for all of them |
| Attack-finding models: exact verification, extended with colliding signatures | [Linear](../lean/Commonware/Symbolic/Linear.lean): keys are integer combinations of member secrets, signatures are integer combinations of hashed inputs, and verification is equality with the summed key applied to the hashed subject |
| Rogue public key, splitting zero | registered keys are any keys; `rogue_key_accepted` and `splitting_zero` instantiate both |
| Proof of possession as a mitigation | a premise of the client's transition; it removes the rogue key and leaves splitting zero |
| Message authenticity | `certificate_authentication`, with the hash collision as an explicit alternative |

The linear attacker (`Derives`) starts from zero, from every signature that an honest member
produced, from every member's proof of possession for its own key and from anything under a
compromised secret, and it adds and scales. `support` shows that a derivable signature involves
the secret of an uncompromised member only at the hash of an input that the secret was applied
to. `attribution` applies it to a certificate that verifies: a flagged member that registered its
own key and is uncompromised signed the subject, or the hash collides.

## What Lean proves

The shared glue in [lean/Commonware/Symbolic](../lean/Commonware/Symbolic) states what a
signature scheme, a committee and a client are to the extracted code (see
[verification/](../README.md)). [Certificate](../lean/Bls/Certificate.lean) proves the following
for every scheme, by induction over the extracted loops:

- `count_eq` and `aggregate_eq`: `count` returns the number of set flags, and `aggregate` returns
  the sum of the keys at the flagged indices in index order, or nothing when a flagged index is
  outside the committee.
- `verify_certificate_iff`, `verify_attestation_iff` and `verify_identity_iff`: each rule returns
  a verdict on every input and accepts exactly when its checks hold.
- `client_step_iff`: the client step is total, accepts exactly a non-empty committee whose `N3f1`
  quorum the certificate meets, and names the committee size and quorum in its event.
- `signer_index_interpretation`, `quorum_authorization` and `subject_binding`: the three target
  properties as consequences of acceptance.
- `quorum_intersection`: two accepted flag lists over one committee share more than
  `(n - 1) / 3` members.

[Protocol](../lean/Bls/Protocol.lean) is trusted. Its `Setup` is the registered keys and the
hash. Members sign subjects, members are compromised, and the `client` is the shared `accept`
action over the extracted `client_step`. The attacker submits a subject, flags and a signature;
the transition's precondition is that the signature and a proof of possession for every flagged
key are derivable from the trace so far. The event invariant `Authentic` gives
[the statements](../lean/Bls/SecurityTheorems.lean):

- `certificate_authentication`: a logged certificate spans the committee and flags its quorum,
  and each flagged member that registered its own key and is uncompromised at acceptance signed
  the subject strictly earlier, or the hash collides.
- `collision_free_certificate_authentication`: with an injective hash the signing event exists.
- `certificates_share_a_signer`: two logged certificates share a member that signed both
  subjects, when at most `(n - 1) / 3` members are faulty and the hash is injective.
- `honest_certificate`: after a quorum of members with their own keys signed a subject, their
  certificate is derivable and accepted.

[SanityChecks](../lean/Bls/SanityChecks.lean) instantiates a committee of four with an injective
hash and proves the client's decisions on a quorum, a sub-quorum, flags of the wrong length and
another subject. `rogue_key_accepted` registers a key that cancels an honest member's secret:
without a proof of possession, a certificate is accepted for that member, who never signed, and
the rogue key has no derivable proof of possession. `splitting_zero` registers two keys that sum
to zero, both with derivable proofs of possession: one signature is accepted with five flags and
with seven. [Audit](../lean/Bls/Audit.lean) checks that every theorem in `Bls` and
`Commonware.Symbolic` depends only on Lean's standard axioms.

[mutations.toml](mutations.toml), run by [mutate.py](../mutate.py), re-extracts the crate after
skipping the length check, accepting one signer below the quorum, counting unflagged members,
skipping the flagged keys or the first member, accepting a signature that does not decode,
swapping namespace and message, ignoring an attestation's signer index, halving the client's
fault tolerance or skipping the rules in the client. Each breaks `Bls.Certificate`.

## Four further properties

None is proved. This is what the development shows about each, and what it would take.

| Property | Finding | What it needs |
| --- | --- | --- |
| Exact signer-set binding: one signature verifies under one set of flags | False over all members, and proof of possession does not help: `splitting_zero`. It holds on honest members, because proof of possession gives every other flagged key zero weight on an honest secret, so two flag sets that verify one signature agree on every member that registered its own key and is uncompromised. | Honest members: no refactor, a short extension of `attribution`. All members: a scheme change, such as signing the signer set in a second round or augmenting each signed message with the signer's key, which costs the single pairing check on a combined key. |
| Threshold participation soundness: a valid threshold certificate needs a quorum of partial signatures | Not a property of verification code, which makes one check under the group key and never sees who took part. It is a property of the scheme and its setup. | The `verify_identity` seam exists. On top of it, a stated attacker rule in the style of [Cremers, Peltonen and Zhao](https://eprint.iacr.org/2024/1920) (a group signature is derivable only from a quorum of partial signatures or compromised shares), or a derivation from Shamir sharing over a field, which needs polynomial interpolation from Mathlib; the model here uses integer coefficients and no Mathlib. Both assume that the sharing's degree is the quorum less one, which a certificate verifier cannot check. Partial-signature verification would also move into `rules.rs`. |
| Every submitted component was valid: each signature in an aggregate verified on its own | False for a received certificate by design: it carries one aggregate, assembly does not verify its inputs, and invalid components can cancel. It can hold only for the party that assembled the certificate from attestations it verified. | Lift attestation checking and assembly out of the parallel batch plumbing into `rules.rs`, then prove that an assembled certificate combines exactly the attestations that `verify_attestation` accepted. Batch verification with random scalars would be read as its per-attestation meaning, with its error probability outside the symbolic model. Third parties need a certificate format that carries the components. |
| Signature uniqueness: one signature verifies for a key and a subject | Holds for attestations and threshold certificates as an algebraic fact about the pairing equation. The current theorems cannot state it: for any scheme `check` is an arbitrary function, and in the linear model verification is equality, so uniqueness there is built in. For multisignature certificates it holds for fixed flags only. | A second reading of the extracted `Terms`, with keys and points in a prime-order group and `check` as a non-degenerate pairing equation. No production change beyond the seam. Decoding must keep rejecting points outside the prime-order subgroup, which is outside the extraction. |

## Review boundary

Review the shared boundary listed in [verification/](../README.md) once. BLS adds `rules.rs`,
`bls.rs`, the definitions in `Signing.lean` and `Linear.lean` (`Signing`, `Roster`, `Flags`,
`Reads`, `selected`, `named`; `Key`, `basis`, `Input`, `term`, `Derives`, `Origin`, `scheme`),
`Checks`, `Accepts` and `quorum` in `Certificate.lean`, the setup, events, transitions with their
precondition, invariant and `#combine` configuration in `Protocol.lean`, and the statements in
`SecurityTheorems.lean`. Lean checks the proofs. The production adapters in `certificate/mod.rs`
and `multisig/mod.rs` are outside the extraction and covered by the differential tests.
