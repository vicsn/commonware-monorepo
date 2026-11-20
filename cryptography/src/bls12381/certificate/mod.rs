//! BLS12-381 certificate scheme implementations.
//!
//! This module provides two signing scheme implementations:
//!
//! - [`multisig`]: Multi-signature scheme with attributable signatures
//! - [`threshold`]: Threshold signature scheme with non-attributable signatures

pub mod multisig;
mod rules;
pub mod threshold;

use crate::{
    bls12381::primitives::{
        ops::{self, aggregate},
        sharing::Sharing,
        variant::Variant,
    },
    certificate::{AssemblyError, Signers},
};
use commonware_codec::types::lazy::Lazy;
use commonware_math::algebra::Additive;
use commonware_utils::Participant;
use core::marker::PhantomData;

/// Builds [`Signers`] using the sharing's participant bound and recovery threshold.
impl<'a, V, I> TryFrom<(&'a Sharing<V>, I)> for Signers
where
    V: Variant,
    I: IntoIterator<Item = Participant>,
{
    type Error = AssemblyError;

    fn try_from((quorum, signers): (&'a Sharing<V>, I)) -> Result<Self, Self::Error> {
        Self::new(quorum.total().get(), signers)?.require(quorum.required())
    }
}

/// The group operations of the variant `V`, as the terms that the certificate rules check with.
struct Pairing<V>(PhantomData<V>);

impl<V> Pairing<V> {
    const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<V: Variant> rules::Terms for Pairing<V> {
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

impl rules::Signers for Signers {
    fn bound(&self) -> u64 {
        self.len() as u64
    }

    fn names(&self, index: u64) -> bool {
        self.contains(index)
    }
}

/// The lazily decoded signature of one key.
struct Single<'a, V: Variant>(&'a Lazy<V::Signature>);

impl<V: Variant> rules::Decoded<V::Signature> for Single<'_, V> {
    fn decoded(&self) -> Option<&V::Signature> {
        self.0.get()
    }
}

/// The lazily decoded signature of several keys.
struct Aggregated<'a, V: Variant>(&'a Lazy<aggregate::Signature<V>>);

impl<V: Variant> rules::Decoded<V::Signature> for Aggregated<'_, V> {
    fn decoded(&self) -> Option<&V::Signature> {
        self.0.get().map(aggregate::Signature::inner)
    }
}
