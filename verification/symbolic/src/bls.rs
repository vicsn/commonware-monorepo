//! A client that accepts BLS12-381 multisig certificates of one committee.
//!
//! Production asks its fault model for the quorum of a committee before it counts the signers of
//! a certificate. This module supplies that arithmetic for the `N3f1` model, where a committee of
//! `n` members tolerates `(n - 1) / 3` faults. The certificate rules come from production.

use crate::rules::{self, Committee, Decoded, Signers, Terms};

/// A committee whose quorum is all but the faults that `N3f1` tolerates.
pub(crate) struct N3f1<'a, C>(pub(crate) &'a C);

impl<K, C: Committee<K>> Committee<K> for N3f1<'_, C> {
    fn members(&self) -> u64 {
        self.0.members()
    }

    fn quorum(&self) -> u64 {
        let members = self.0.members();
        members - (members - 1) / 3
    }

    fn key(&self, index: u64) -> Option<&K> {
        self.0.key(index)
    }
}

/// The event a client logs after accepting a certificate.
pub(crate) struct Certified {
    /// Size of the committee the certificate was checked against.
    pub(crate) members: u64,
    /// Number of signers that the committee requires.
    pub(crate) quorum: u64,
}

/// Accept the certificate (`signers`, `signature`) for `message` in `namespace` if the production
/// rules accept it for the trusted `committee` with its `N3f1` quorum. Returns the event to log,
/// or `None`. An empty committee accepts nothing.
pub(crate) fn client_step<T, C, B, S>(
    terms: &T,
    committee: &C,
    namespace: &[u8],
    message: &[u8],
    signers: &B,
    signature: &S,
) -> Option<Certified>
where
    T: Terms,
    C: Committee<T::Public>,
    B: Signers,
    S: Decoded<T::Point>,
{
    let committee = N3f1(committee);
    let members = committee.members();
    if members == 0 {
        return None;
    }
    if rules::verify_certificate(terms, &committee, signers, signature, namespace, message) {
        Some(Certified {
            members,
            quorum: committee.quorum(),
        })
    } else {
        None
    }
}

#[cfg(test)]
mod tests;
