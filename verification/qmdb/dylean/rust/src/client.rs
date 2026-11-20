//! A client that accepts one claimed item of an MMR with one peak.
//!
//! The production verifier lays out peaks with its `Blueprint` and folds them into a root. An MMR
//! with `2^height` leaves has a single peak at position `2 * (2^height - 1)` that covers every
//! leaf, so with forward-fold bagging and no inactive peaks its root is `root(domain, 2^height, 0,
//! peak)`. This module supplies that layout and the MMR child positions; the traversal, its
//! callbacks and every hash input come from production.

use crate::{
    terms::{self, Terms},
    traversal::{self, Nodes, Opening},
};

/// Domain byte of the MMR family.
pub(crate) const MMR_DOMAIN: u8 = 0;

/// Domain byte of forward-fold peak bagging.
pub(crate) const FORWARD_FOLD: u8 = 0;

/// Largest height whose `2^height` leaves fit the production MMR limit of `2^62`.
pub(crate) const MAX_HEIGHT: u32 = 62;

/// MMR nodes hashed with the production encodings.
pub(crate) struct Mmr<'a, T>(&'a T);

impl<T: Terms> Nodes for Mmr<'_, T> {
    type Digest = T::Digest;

    fn children(&self, position: u64, height: u32) -> (u64, u64) {
        (position - (1u64 << height), position - 1)
    }

    fn leaf_digest(&self, position: u64, element: &[u8]) -> T::Digest {
        terms::leaf_digest(self.0, position, element)
    }

    fn node_digest(&self, position: u64, left: &T::Digest, right: &T::Digest) -> T::Digest {
        terms::node_digest(self.0, position, left, right)
    }
}

/// The claimed item, as an element of the traversal.
pub(crate) struct Element<'a>(&'a [u8]);

impl AsRef<[u8]> for Element<'_> {
    fn as_ref(&self) -> &[u8] {
        self.0
    }
}

/// The claimed item, as the traversal's element source.
pub(crate) struct Single<'a>(Option<&'a [u8]>);

impl<'a> Iterator for Single<'a> {
    type Item = Element<'a>;

    fn next(&mut self) -> Option<Element<'a>> {
        match self.0 {
            Some(item) => {
                self.0 = None;
                Some(Element(item))
            }
            None => None,
        }
    }
}

/// Accept `item` at `location` of an MMR with `2^height` leaves and root `root` if the production
/// traversal rebuilds the peak from `siblings`, reads all of them, and the production root
/// encoding of the peak is `root`.
///
/// The traversal reads exactly one element on success, so no element can be left over.
pub(crate) fn verify<T: Terms>(
    terms: &T,
    height: u32,
    location: u64,
    root: &T::Digest,
    item: &[u8],
    siblings: &[T::Digest],
) -> bool {
    if height > MAX_HEIGHT {
        return false;
    }
    let leaves = 1u64 << height;
    if location >= leaves {
        return false;
    }
    let mut opening = Opening::new(Mmr(terms), Single(Some(item)), siblings, 0, ());
    match traversal::reconstruct(
        &mut opening,
        2 * (leaves - 1),
        leaves,
        0,
        location,
        location + 1,
    ) {
        Ok(peak) => {
            opening.cursor() == siblings.len()
                && terms::root(terms, [MMR_DOMAIN, FORWARD_FOLD], leaves, 0, &peak) == *root
        }
        Err(_) => false,
    }
}

/// Terms that can also carry a claimed item in a received message.
pub(crate) trait Messages: Terms {
    /// A received message.
    type Message;

    /// The item that `message` carries, if any.
    fn parse<'a>(&self, message: &'a Self::Message) -> Option<&'a [u8]>;
}

/// The event a client logs after accepting an item.
pub(crate) struct Acceptance<'a> {
    /// Height of the snapshot the item was checked against.
    pub(crate) height: u32,
    /// Claimed location of the item.
    pub(crate) location: u64,
    /// The accepted item.
    pub(crate) item: &'a [u8],
}

/// Accept the item in `message` at `location` of the snapshot with `2^height` leaves and trusted
/// `root` if [`verify`] accepts `siblings` as its opening. Returns the event to log, or `None`.
pub(crate) fn client_step<'a, T: Messages>(
    terms: &T,
    root: &T::Digest,
    height: u32,
    message: &'a T::Message,
    location: u64,
    siblings: &[T::Digest],
) -> Option<Acceptance<'a>> {
    match terms.parse(message) {
        None => None,
        Some(item) => {
            if verify(terms, height, location, root, item, siblings) {
                Some(Acceptance {
                    height,
                    location,
                    item,
                })
            } else {
                None
            }
        }
    }
}
