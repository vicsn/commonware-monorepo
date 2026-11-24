//! Node positions and peaks of an MMR as `u64` arithmetic.
//!
//! [`super::Family`] and [`super::iterator::PeakIterator`] forward to these functions. They use no
//! Merkle types, so the symbolic verification extracts this file unchanged.

/// Domain tag committed by every MMR root.
pub(crate) const DOMAIN: u8 = 0;

/// Maximum valid location (leaf count): `2^62`.
pub(crate) const MAX_LEAVES: u64 = 0x4000_0000_0000_0000;

/// Positions of the left and right children of the node at `pos`, whose subtree has `2^height`
/// leaves.
pub(crate) const fn children(pos: u64, height: u32) -> (u64, u64) {
    (pos - (1 << height), pos - 1)
}

/// Number of leaves appended after the leftmost leaf of a node of `height` before the node exists.
///
/// # Panics
///
/// Panics if `height` is excessively large.
pub(crate) const fn birth_offset(height: u32) -> u64 {
    assert!(height < u64::BITS, "height excessively large");
    1 << height
}

/// The peaks of an MMR, yielded as `(position, height)` in decreasing order of height.
///
/// An MMR with `leaves` leaves has one perfect subtree per set bit of `leaves`, tallest first. A
/// subtree of height `h` holds `2^(h+1) - 1` nodes and its root is the last of them.
#[derive(Default)]
pub(crate) struct Peaks {
    /// The number of leaves in the MMR.
    leaves: u64,
    /// The bit of `leaves` above which every peak has been yielded.
    height: u32,
    /// The number of nodes in the peaks yielded so far.
    nodes: u64,
}

impl Peaks {
    /// The peaks of an MMR with `leaves` leaves.
    pub(crate) const fn new(leaves: u64) -> Self {
        Self {
            leaves,
            height: u64::BITS,
            nodes: 0,
        }
    }

    /// The next peak as `(position, height)`, or `None` after the shortest.
    pub(crate) const fn next(&mut self) -> Option<(u64, u32)> {
        while self.height > 0 {
            self.height -= 1;
            if (self.leaves >> self.height) & 1 == 1 {
                let size = (1u64 << (self.height + 1)) - 1;
                let peak = self.nodes + size - 1;
                self.nodes += size;
                return Some((peak, self.height));
            }
        }
        None
    }
}
