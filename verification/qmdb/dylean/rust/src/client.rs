//! The client's decision for one inclusion claim.

use crate::{
    adapter, spec,
    terms::{Store, Terms},
};

/// The event a client logs after accepting an item.
pub struct Acceptance<I> {
    /// Height of the snapshot the item was checked against.
    pub height: u32,
    /// Claimed location of the item.
    pub location: u64,
    /// The accepted item.
    pub item: I,
}

/// Accept `message` as the item at `location` of the snapshot in `store`, which has `2^height`
/// leaves, if `siblings` opens it under the snapshot's honest root.
///
/// The production traversal rebuilds the peak. Returns the event to log, or `None` to reject.
pub fn client_step<T: Terms, S: Store<T::Item>>(
    store: &S,
    height: u32,
    message: &T::Bytes,
    location: u64,
    siblings: &[T::Digest],
) -> Option<Acceptance<T::Item>> {
    match T::parse(message) {
        None => None,
        Some(item) => {
            if height > spec::MAX_HEIGHT {
                None
            } else {
                let root = spec::root::<T, S>(store, height);
                if adapter::verify::<T>(height, location, &root, &item, siblings) {
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
}
