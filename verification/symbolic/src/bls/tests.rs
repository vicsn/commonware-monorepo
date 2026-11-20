//! Differential tests of the BLS client against production multisig certificates.
//!
//! The client, which runs the production certificate rules with its own `N3f1` quorum, and the
//! production scheme must return the same verdict on honest certificates and on ones with too few
//! signers, a bitmap of the wrong length, another namespace or message, a signature that misses a
//! named signer or includes an unnamed one, and a signature that does not decode. The quorum
//! arithmetic must agree with production's `N3f1`.

use crate::{
    bls::{self, N3f1},
    concrete::Curve,
    rules::{self, Committee},
};
use bytes::Bytes;
use commonware_codec::types::lazy::Lazy;
use commonware_cryptography::{
    Signer as _,
    bls12381::{
        certificate::multisig::Certificate,
        primitives::{
            group::Private,
            ops::{self, aggregate},
            variant::{MinPk, MinSig, Variant},
        },
    },
    certificate::{Attestation, Scheme as _, Signers, Subject, Verifier as _},
    ed25519,
    sha256::Digest,
};
use commonware_math::algebra::{Additive, Random};
use commonware_parallel::Sequential;
use commonware_utils::{
    Faults, N3f1 as Production, Participant, TryCollect as _, non_empty, ordered::BiMap, test_rng,
};
use core::marker::PhantomData;
use rand_core::CryptoRng;

const NAMESPACE: &[u8] = b"symbolic-bls-certificate";
const OTHER_NAMESPACE: &[u8] = b"symbolic-bls-other";
const MESSAGE: &[u8] = b"subject";
const OTHER_MESSAGE: &[u8] = b"another subject";

/// A subject that is its message, under the scheme's namespace.
#[derive(Clone, Debug)]
pub struct Message(&'static [u8]);

impl Subject for Message {
    type Namespace = Vec<u8>;

    fn namespace<'a>(&self, derived: &'a Self::Namespace) -> &'a [u8] {
        derived
    }

    fn message(&self) -> Bytes {
        Bytes::from_static(self.0)
    }
}

// The production scheme over `Message` with the `N3f1` fault model.
mod scheme {
    use super::Message;
    use commonware_utils::N3f1;

    commonware_cryptography::impl_certificate_bls12381_multisig!(Message, Vec<u8>, N3f1);
}

type Scheme<V> = scheme::Scheme<ed25519::PublicKey, V>;

/// A committee of `n` members: its signing keys and public keys in member order, and the
/// production participants.
struct Fixture<V: Variant> {
    privates: Vec<Private>,
    publics: Vec<V::Public>,
    participants: BiMap<ed25519::PublicKey, V::Public>,
}

fn fixture<V: Variant>(rng: &mut impl CryptoRng, n: u32) -> Fixture<V> {
    let keys: Vec<Private> = (0..n).map(|_| Private::random(&mut *rng)).collect();
    let participants: BiMap<ed25519::PublicKey, V::Public> = keys
        .iter()
        .map(|key| {
            (
                ed25519::PrivateKey::random(&mut *rng).public_key(),
                ops::compute_public::<V>(key),
            )
        })
        .try_collect()
        .unwrap();
    // Production orders members by identity key.
    let publics: Vec<V::Public> = (0..n as usize)
        .map(|index| *participants.value(index).unwrap())
        .collect();
    let privates = publics
        .iter()
        .map(|public| {
            keys.iter()
                .find(|key| ops::compute_public::<V>(key) == *public)
                .unwrap()
                .clone()
        })
        .collect();
    Fixture {
        privates,
        publics,
        participants,
    }
}

/// One certificate claim.
struct Claim {
    name: &'static str,
    /// Length of the signer bitmap.
    bound: u32,
    /// Members that the certificate names.
    named: Vec<u32>,
    /// Members whose signatures over `MESSAGE` in `NAMESPACE` are combined.
    signed: Vec<u32>,
    /// Whether the signature decodes.
    decodes: bool,
    namespace: &'static [u8],
    message: &'static [u8],
    accepted: bool,
}

fn claims(n: u32) -> Vec<Claim> {
    let quorum = Production::quorum(n);
    let honest = |name, named: Vec<u32>| Claim {
        name,
        bound: n,
        signed: named.clone(),
        named,
        decodes: true,
        namespace: NAMESPACE,
        message: MESSAGE,
        accepted: true,
    };
    let first: Vec<u32> = (0..quorum).collect();
    let last: Vec<u32> = (n - quorum..n).collect();
    let mut claims = vec![
        honest("first quorum", first.clone()),
        honest("last quorum", last.clone()),
        honest("everyone", (0..n).collect()),
        Claim {
            name: "longer bitmap",
            bound: n + 1,
            accepted: false,
            ..honest("", first.clone())
        },
        Claim {
            name: "other namespace",
            namespace: OTHER_NAMESPACE,
            accepted: false,
            ..honest("", first.clone())
        },
        Claim {
            name: "other message",
            message: OTHER_MESSAGE,
            accepted: false,
            ..honest("", first.clone())
        },
        Claim {
            name: "undecodable signature",
            decodes: false,
            accepted: false,
            ..honest("", first.clone())
        },
    ];
    if quorum > 1 {
        claims.push(Claim {
            name: "below quorum",
            accepted: false,
            ..honest("", (0..quorum - 1).collect())
        });
        claims.push(Claim {
            name: "missing signature",
            signed: (1..quorum).collect(),
            accepted: false,
            ..honest("", first.clone())
        });
        claims.push(Claim {
            name: "shorter bitmap",
            bound: n - 1,
            accepted: false,
            ..honest("", (0..quorum.min(n - 1)).collect())
        });
    }
    if quorum < n {
        claims.push(Claim {
            name: "unnamed signature",
            signed: (0..=quorum).collect(),
            accepted: false,
            ..honest("", first.clone())
        });
        claims.push(Claim {
            name: "other signers",
            signed: last,
            accepted: false,
            ..honest("", first)
        });
    }
    claims
}

/// Check every claim of committees of several sizes and return the number of claims.
fn agree<V: Variant>() -> usize {
    let mut rng = test_rng();
    let mut checked = 0;
    for n in [1u32, 2, 3, 4, 5, 6, 7, 10, 13] {
        let fixture = fixture::<V>(&mut rng, n);
        for claim in claims(n) {
            let signatures: Vec<V::Signature> = claim
                .signed
                .iter()
                .map(|member| {
                    ops::sign_message::<V>(&fixture.privates[*member as usize], NAMESPACE, MESSAGE)
                })
                .collect();

            // Production: the scheme's verifier for the claimed namespace.
            let verifier = Scheme::<V>::verifier(claim.namespace, fixture.participants.clone());
            let signature = if claim.decodes {
                Lazy::from(aggregate::combine_signatures::<V, _>(
                    non_empty![@signatures.iter()],
                ))
            } else {
                Lazy::deferred(&mut Bytes::from_static(&[0u8]), ())
            };
            let certificate = Certificate::<V> {
                signers: Signers::new(
                    claim.bound,
                    claim.named.iter().map(|member| Participant::new(*member)),
                )
                .unwrap(),
                signature,
            };
            let production = verifier.verify_certificate::<_, Digest>(
                &mut rng,
                Message(claim.message),
                &certificate,
                &Sequential,
            );

            // The client: the same keys, bitmap and signature.
            let mut bits = vec![false; claim.bound as usize];
            for member in &claim.named {
                bits[*member as usize] = true;
            }
            let mut sum = V::Signature::zero();
            for signature in &signatures {
                sum += signature;
            }
            let client = bls::client_step(
                &Curve::<V>(PhantomData),
                &fixture.publics,
                claim.namespace,
                claim.message,
                &bits,
                &claim.decodes.then_some(sum),
            );

            assert_eq!(production, claim.accepted, "{} of {n}", claim.name);
            assert_eq!(client.is_some(), production, "{} of {n}", claim.name);
            if let Some(event) = client {
                assert_eq!(event.members, u64::from(n));
                assert_eq!(event.quorum, u64::from(Production::quorum(n)));
            }
            checked += 1;
        }
    }
    checked
}

#[test]
fn client_agrees_with_production_certificates() {
    assert_eq!(agree::<MinPk>() + agree::<MinSig>(), 198);
}

/// A member's own signature is accepted for its index and for no other.
fn attest<V: Variant>() -> usize {
    let mut rng = test_rng();
    let mut checked = 0;
    for n in [1u32, 4, 7] {
        let fixture = fixture::<V>(&mut rng, n);
        let verifier = Scheme::<V>::verifier(NAMESPACE, fixture.participants.clone());
        let signature = ops::sign_message::<V>(&fixture.privates[0], NAMESPACE, MESSAGE);
        for (signer, message, accepted) in [
            (0, MESSAGE, true),
            (0, OTHER_MESSAGE, false),
            (n - 1, MESSAGE, n == 1),
            (n, MESSAGE, false),
        ] {
            let production = verifier.verify_attestation::<_, Digest>(
                &mut rng,
                Message(message),
                &Attestation {
                    signer: Participant::new(signer),
                    signature: Lazy::from(signature),
                },
                &Sequential,
            );
            let rules = rules::verify_attestation(
                &Curve::<V>(PhantomData),
                &fixture.publics,
                u64::from(signer),
                &Some(signature),
                NAMESPACE,
                message,
            );
            assert_eq!(production, accepted, "signer {signer} of {n}");
            assert_eq!(rules, production, "signer {signer} of {n}");
            checked += 1;
        }
    }
    checked
}

#[test]
fn rules_agree_with_production_attestations() {
    assert_eq!(attest::<MinPk>() + attest::<MinSig>(), 24);
}

/// A committee of a given size without keys.
struct Sized(u64);

impl Committee<()> for Sized {
    fn members(&self) -> u64 {
        self.0
    }

    fn quorum(&self) -> u64 {
        self.0
    }

    fn key(&self, _: u64) -> Option<&()> {
        None
    }
}

#[test]
fn quorum_agrees_with_production() {
    for members in 1..=100_000u32 {
        assert_eq!(
            N3f1(&Sized(u64::from(members))).quorum(),
            u64::from(Production::quorum(members)),
        );
    }
}
