//! The smallest client: it accepts a message whose production leaf digest is a trusted commitment.
//!
//! The commitment is the digest of one leaf at position 0. The only production code involved is
//! `terms::leaf_digest`, so this target shows the whole route from a production function to a
//! DyLean trace theorem with as little else as possible.

use crate::{
    client::Messages,
    terms::{self, Terms},
};

/// Position of the committed leaf.
pub(crate) const POSITION: u64 = 0;

/// The event a client logs after accepting an item.
pub(crate) struct Acceptance<'a> {
    /// The accepted item.
    pub(crate) item: &'a [u8],
}

/// Accept the item in `message` if its production leaf digest at [`POSITION`] is `commitment`.
/// Returns the event to log, or `None`.
pub(crate) fn client_step<'a, T: Terms + Messages>(
    terms: &T,
    commitment: &T::Digest,
    message: &'a T::Message,
) -> Option<Acceptance<'a>> {
    match terms.parse(message) {
        None => None,
        Some(item) => {
            if terms::leaf_digest(terms, POSITION, item) == *commitment {
                Some(Acceptance { item })
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod tests;
