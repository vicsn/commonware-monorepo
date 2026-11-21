//! Differential tests of the leaf client against the production hasher.
//!
//! The commitment that the client checks must be the digest that production computes for the
//! leaf, and the client must accept exactly the committed item.

use crate::{
    concrete::{Concrete, bytes},
    leaf,
};
use commonware_cryptography::Sha256;
use commonware_storage::merkle::{
    Bagging,
    hasher::Hasher as _,
    mmr::{Position, StandardHasher},
};
use commonware_utils::test_rng;
use rand::Rng as _;

fn commitment(item: &[u8]) -> [u8; 32] {
    let hasher = StandardHasher::<Sha256>::new(Bagging::ForwardFold);
    bytes(&hasher.leaf_digest(Position::new(leaf::POSITION), item))
}

#[test]
fn client_accepts_exactly_the_committed_item() {
    let mut rng = test_rng();
    for length in 0..64usize {
        let mut item = vec![0u8; length];
        rng.fill_bytes(&mut item);
        let trusted = commitment(&item);

        let accepted = leaf::client_step(&Concrete, &trusted, &item).expect("committed item");
        assert_eq!(accepted.item, item);

        let mut longer = item.clone();
        longer.push(0);
        assert!(leaf::client_step(&Concrete, &trusted, &longer).is_none());
        if let Some(last) = item.last_mut() {
            *last ^= 1;
            assert!(leaf::client_step(&Concrete, &trusted, &item).is_none());
        }
    }
}
