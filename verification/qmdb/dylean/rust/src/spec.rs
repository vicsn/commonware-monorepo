//! Single-item inclusion in an MMR with `2^height` leaves and one peak.
//!
//! Positions follow MMR numbering. The peak sits at position `2 * (2^height - 1)`. A node at
//! `position` whose subtree holds `2^h` leaves has its children at `position - 2^h` and
//! `position - 1`. An opening lists the sibling digests in the order of a left-first depth-first
//! traversal. All functions require `height <= MAX_HEIGHT`, which keeps every position in `u64`.

use crate::terms::{Store, Terms};

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

/// Root of the MMR: `H(MMR_DOMAIN || FORWARD_FOLD || be64(2^height) || peak)`.
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

/// Digest of the honest subtree of `height` at `position` whose first leaf is at `start`.
pub fn tree<T: Terms, S: Store<T::Item>>(
    store: &S,
    height: u32,
    position: u64,
    start: u64,
) -> T::Digest {
    if height == 0 {
        let item = store.item(start);
        leaf::<T>(position, &item)
    } else {
        let half = 1u64 << (height - 1);
        let left = tree::<T, S>(store, height - 1, position - 2 * half, start);
        let right = tree::<T, S>(store, height - 1, position - 1, start + half);
        node::<T>(position, left, right)
    }
}

/// Honest root of the snapshot.
pub fn root<T: Terms, S: Store<T::Item>>(store: &S, height: u32) -> T::Digest {
    let leaves = 1u64 << height;
    wrap::<T>(height, tree::<T, S>(store, height, 2 * (leaves - 1), 0))
}

/// Rebuild the subtree of `height` at `position` that contains `location`.
///
/// Reads siblings from `siblings[next..]` and returns the subtree digest with the index of the
/// first unread sibling, or `None` if the opening is too short.
// Explicit matches keep the failure branches visible to extraction.
#[allow(clippy::manual_map)]
pub fn replay<T: Terms>(
    item: &T::Item,
    height: u32,
    position: u64,
    start: u64,
    location: u64,
    siblings: &[T::Digest],
    next: usize,
) -> Option<(T::Digest, usize)> {
    if height == 0 {
        Some((leaf::<T>(position, item), next))
    } else {
        let half = 1u64 << (height - 1);
        if location < start + half {
            match replay::<T>(
                item,
                height - 1,
                position - 2 * half,
                start,
                location,
                siblings,
                next,
            ) {
                None => None,
                Some((left, after)) => {
                    if after < siblings.len() {
                        let right = siblings[after];
                        Some((node::<T>(position, left, right), after + 1))
                    } else {
                        None
                    }
                }
            }
        } else if next < siblings.len() {
            let left = siblings[next];
            match replay::<T>(
                item,
                height - 1,
                position - 1,
                start + half,
                location,
                siblings,
                next + 1,
            ) {
                None => None,
                Some((right, after)) => Some((node::<T>(position, left, right), after)),
            }
        } else {
            None
        }
    }
}

/// Accept `item` at `location` under `root` if the opening rebuilds the root and is fully used.
pub fn verify_single<T: Terms>(
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
    match replay::<T>(item, height, 2 * (leaves - 1), 0, location, siblings, 0) {
        Some((peak, used)) => used == siblings.len() && wrap::<T>(height, peak) == *root,
        None => false,
    }
}
