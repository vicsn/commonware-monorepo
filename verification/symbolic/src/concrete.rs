//! Concrete instances for differential tests against production: hash inputs concatenated and
//! hashed with SHA-256, messages that carry their own bytes, and BLS12-381 keys and signatures
//! with production's hashing and pairing check.

use crate::{
    client::Messages,
    rules,
    terms::{Part, Terms},
};
use commonware_cryptography::{
    Hasher as _, Sha256,
    bls12381::primitives::{ops, variant::Variant},
    sha256,
};
use commonware_math::algebra::Additive;
use core::marker::PhantomData;

/// SHA-256 over concatenated parts, with byte-string messages.
pub(crate) struct Concrete;

impl Terms for Concrete {
    type Digest = [u8; 32];

    fn hash(&self, parts: &[Part<'_, [u8; 32]>]) -> [u8; 32] {
        let mut input = Vec::new();
        for part in parts {
            match part {
                Part::Bytes(part) => input.extend_from_slice(part),
                Part::Digest(digest) => input.extend_from_slice(*digest),
            }
        }
        bytes(&Sha256::hash(&[&input]))
    }
}

impl Messages for Concrete {
    type Message = Vec<u8>;

    fn parse<'a>(&self, message: &'a Vec<u8>) -> Option<&'a [u8]> {
        Some(message)
    }
}

/// The bytes of a production digest.
pub(crate) fn bytes(digest: &sha256::Digest) -> [u8; 32] {
    digest.as_ref().try_into().unwrap()
}

/// BLS12-381 keys and signatures of the variant `V`, hashed and checked as production does.
pub(crate) struct Curve<V>(pub(crate) PhantomData<V>);

impl<V: Variant> rules::Terms for Curve<V> {
    type Public = V::Public;
    type Point = V::Signature;

    fn zero(&self) -> V::Public {
        V::Public::zero()
    }

    fn add(&self, mut sum: V::Public, key: &V::Public) -> V::Public {
        sum += key;
        sum
    }

    fn message(&self, namespace: &[u8], message: &[u8]) -> V::Signature {
        ops::hash_with_namespace::<V>(V::MESSAGE, namespace, message)
    }

    fn check(&self, key: &V::Public, hashed: &V::Signature, signature: &V::Signature) -> bool {
        V::verify(key, hashed, signature).is_ok()
    }
}

/// A committee given by its keys in member order. On its own it requires every member.
impl<K> rules::Committee<K> for Vec<K> {
    fn members(&self) -> u64 {
        self.len() as u64
    }

    fn quorum(&self) -> u64 {
        self.len() as u64
    }

    fn key(&self, index: u64) -> Option<&K> {
        self.get(usize::try_from(index).ok()?)
    }
}

/// Signer flags, one per index.
impl rules::Signers for Vec<bool> {
    fn bound(&self) -> u64 {
        self.len() as u64
    }

    fn names(&self, index: u64) -> bool {
        self[index as usize]
    }
}

/// A signature that decoded, or none.
impl<T> rules::Decoded<T> for Option<T> {
    fn decoded(&self) -> Option<&T> {
        self.as_ref()
    }
}
