//! A QMDB client that accepts one claimed item of an operations tree whose `2^height` leaves form
//! one MMR peak.
//!
//! The client runs the production range-proof reconstruction over the production MMR geometry,
//! with the bagging of QMDB's operation roots. Every peak, sibling, hash input and the root
//! encoding comes from production; this module fixes only the claim's shape: one item, no inactive
//! peaks, and the bound on the height.

use crate::{
    client::Messages,
    geometry::Mmr,
    mmr_geometry,
    reconstruct::{self, Single, StandardNodes},
    terms::Terms,
    BACKWARD_FOLD,
};

/// Largest height whose `2^height` leaves fit production's `mmr::Family::MAX_LEAVES`.
pub(crate) const MAX_HEIGHT: u32 = 62;

/// Accept `item` at `location` of an MMR with `2^height` leaves and root `root` if the production
/// reconstruction of a range proof of that one item, with `siblings` as its digests, returns
/// `root`.
pub(crate) fn verify_element_inclusion<T: Terms>(
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
    match reconstruct::reconstruct(
        &Mmr,
        terms,
        StandardNodes::new(&Mmr, terms),
        [mmr_geometry::DOMAIN, BACKWARD_FOLD],
        true,
        1u64 << height,
        0,
        siblings,
        location,
        1,
        Single::new(item),
        (),
    ) {
        Ok(rebuilt) => rebuilt == *root,
        Err(_) => false,
    }
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
/// `root` if [`verify_element_inclusion`] accepts `siblings` as its opening. Returns the event to log, or `None`.
pub(crate) fn accept_inclusion<'a, T: Terms + Messages>(
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
            if verify_element_inclusion(terms, height, location, root, item, siblings) {
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

#[cfg(test)]
mod tests;
