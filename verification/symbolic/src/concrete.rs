//! Concrete instances for differential tests against production: hash inputs concatenated and
//! hashed with SHA-256, and messages that carry their own bytes.

use crate::{
    client::Messages,
    terms::{Part, Terms},
};
use commonware_cryptography::{Hasher as _, Sha256, sha256};

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
