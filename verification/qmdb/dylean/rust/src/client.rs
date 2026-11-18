//! The client's decision for one inclusion claim.

use crate::{adapter, terms::Terms};

/// The event a client logs after accepting an item.
pub struct Acceptance<I> {
    /// Height of the snapshot the item was checked against.
    pub height: u32,
    /// Claimed location of the item.
    pub location: u64,
    /// The accepted item.
    pub item: I,
}

/// Accept `message` as the item at `location` of the snapshot with `2^height` leaves and trusted
/// `root` if the production traversal verifies `siblings` as its opening.
///
/// Returns the event to log, or `None` to reject.
pub fn client_step<T: Terms>(
    root: &T::Digest,
    height: u32,
    message: &T::Bytes,
    location: u64,
    siblings: &[T::Digest],
) -> Option<Acceptance<T::Item>> {
    match T::parse(message) {
        None => None,
        Some(item) => {
            if adapter::verify::<T>(height, location, root, &item, siblings) {
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
