//! Single-item verification through the pinned production traversal.
//!
//! The production verifier reaches `traversal::reconstruct` through callbacks on its `Hasher`.
//! This module supplies the same callbacks over [`Terms`]: the hash inputs follow the production
//! `Hasher` defaults for an MMR with forward-fold bagging and one peak. Positions follow MMR
//! numbering, so the peak of `2^height` leaves sits at position `2 * (2^height - 1)`.

use crate::{
    terms::Terms,
    traversal::{self, Backend, Error},
};

/// Domain byte of the MMR family.
pub const MMR_DOMAIN: u8 = 0;

/// Domain byte of forward-fold peak bagging.
pub const FORWARD_FOLD: u8 = 0;

/// Largest supported height.
pub const MAX_HEIGHT: u32 = 63;

/// Big-endian encoding of `value`.
pub fn be64(value: u64) -> [u8; 8] {
    [
        (value >> 56) as u8,
        (value >> 48) as u8,
        (value >> 40) as u8,
        (value >> 32) as u8,
        (value >> 24) as u8,
        (value >> 16) as u8,
        (value >> 8) as u8,
        value as u8,
    ]
}

/// Leaf digest: `H(be64(position) || item)`.
pub fn leaf<T: Terms>(position: u64, item: &T::Item) -> T::Digest {
    T::hash(T::concat(T::literal(&be64(position)), T::item(item)))
}

/// Internal node digest: `H(be64(position) || left || right)`.
pub fn node<T: Terms>(position: u64, left: T::Digest, right: T::Digest) -> T::Digest {
    T::hash(T::concat(
        T::literal(&be64(position)),
        T::concat(T::digest(left), T::digest(right)),
    ))
}

/// Root of an MMR with `2^height` leaves:
/// `H(MMR_DOMAIN || FORWARD_FOLD || be64(2^height) || peak)`. Requires `height <= MAX_HEIGHT`.
pub fn wrap<T: Terms>(height: u32, peak: T::Digest) -> T::Digest {
    let leaves = be64(1u64 << height);
    let prefix = [
        MMR_DOMAIN,
        FORWARD_FOLD,
        leaves[0],
        leaves[1],
        leaves[2],
        leaves[3],
        leaves[4],
        leaves[5],
        leaves[6],
        leaves[7],
    ];
    T::hash(T::concat(T::literal(&prefix), T::digest(peak)))
}

/// Traversal callbacks for one item and a cursor over its opening.
pub struct Opening<'a, T: Terms> {
    item: &'a T::Item,
    siblings: &'a [T::Digest],
    next: usize,
}

impl<T: Terms> Backend for Opening<'_, T> {
    type Digest = T::Digest;

    fn children(&self, position: u64, width: u64) -> (u64, u64) {
        (position - width, position - 1)
    }

    fn sibling(&mut self) -> Result<T::Digest, Error> {
        if self.next < self.siblings.len() {
            let digest = self.siblings[self.next];
            self.next += 1;
            Ok(digest)
        } else {
            Err(Error::MissingDigests)
        }
    }

    fn leaf(&mut self, position: u64) -> Result<T::Digest, Error> {
        Ok(leaf::<T>(position, self.item))
    }

    fn node(&self, position: u64, left: T::Digest, right: T::Digest) -> T::Digest {
        node::<T>(position, left, right)
    }

    fn collect(&mut self, _: u64, _: T::Digest, _: u64, _: T::Digest) {}
}

/// Accept `item` at `location` of an MMR with `2^height` leaves and root `root` if the production
/// traversal rebuilds the peak from `siblings`, uses all of them, and the wrapped peak is `root`.
pub fn verify<T: Terms>(
    height: u32,
    location: u64,
    root: &T::Digest,
    item: &T::Item,
    siblings: &[T::Digest],
) -> bool {
    if height > MAX_HEIGHT {
        return false;
    }
    let leaves = 1u64 << height;
    if location >= leaves {
        return false;
    }
    let mut opening = Opening::<T> {
        item,
        siblings,
        next: 0,
    };
    match traversal::reconstruct(
        &mut opening,
        2 * (leaves - 1),
        leaves,
        0,
        location,
        location + 1,
    ) {
        Ok(peak) => opening.next == siblings.len() && wrap::<T>(height, peak) == *root,
        Err(_) => false,
    }
}
