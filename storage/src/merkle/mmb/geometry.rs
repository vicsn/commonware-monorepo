//! Node positions and peaks of an MMB as `u64` arithmetic.
//!
//! [`super::Family`] and [`super::iterator::PeakIterator`] forward to these functions. They use no
//! Merkle types, so the symbolic verification extracts this file unchanged.

/// Domain tag committed by every MMB root.
pub(crate) const DOMAIN: u8 = 1;

/// Maximum valid position (node count): `2^63 - 2` (the size for `2^62 + 30` leaves).
pub(crate) const MAX_NODES: u64 = 0x7FFF_FFFF_FFFF_FFFE;

/// Maximum valid location (leaf count): `2^62 + 30`.
pub(crate) const MAX_LEAVES: u64 = 0x4000_0000_0000_001E;

/// Position of the leaf at location `loc`: `2 * loc - ilog2(loc + 1)`.
pub(crate) const fn location_to_position(loc: u64) -> u64 {
    2 * loc - (loc + 1).ilog2() as u64
}

/// Location of the leaf at position `pos`, or `None` if `pos` is a parent.
pub(crate) const fn position_to_location(pos: u64) -> Option<u64> {
    // Solve 2*N - ilog2(N+1) = pos for N. Starting estimate: N ~ (pos + ilog2(N+1)) / 2 ~ pos/2.
    // One refinement gives accuracy within -1 if the input is a valid leaf position, so the loop
    // body runs at most twice.
    let mut n = pos / 2;
    n = (pos + (n + 1).ilog2() as u64) / 2;
    loop {
        let leaf_pos = 2 * n - (n + 1).ilog2() as u64;
        if leaf_pos == pos {
            return Some(n);
        }
        if leaf_pos > pos {
            // pos falls between two leaf positions, so it is a parent.
            return None;
        }
        n += 1;
    }
}

/// Number of leaves appended after the leftmost leaf of a node of `height` before the node is
/// born.
///
/// # Panics
///
/// Panics if `height` is excessively large.
pub(crate) fn birth_offset(height: u32) -> u64 {
    if height == 0 {
        return 1;
    }

    // Appending the last leaf brings the count to `2^h` past the leftmost leaf, and the merge lags
    // it by `2^(h-1) - 1` leaves.
    assert!(height - 1 < u64::BITS, "height excessively large");
    let half = 1u64 << (height - 1);
    half.checked_mul(3).expect("height excessively large") - 1
}

/// The peaks of an MMB, yielded as `(position, height)` from oldest (leftmost) to newest.
///
/// See [`super::iterator::PeakIterator`] for the order of positions.
#[derive(Default)]
pub(crate) struct Peaks {
    /// The exact number of leaves in the MMB.
    n: u64,
    /// Bit index, counting down from `num_peaks - 1` to 0.
    current_i: u32,
    /// Number of peaks left to yield.
    remaining: u32,
    /// First leaf of the next (rightward) peak.
    start_leaf_cursor: u64,
}

impl Peaks {
    /// The peaks of an MMB with `n` leaves.
    pub(crate) fn new(n: u64) -> Self {
        if n == 0 {
            return Self::default();
        }

        // Exactly `ilog2(N+1)` peaks total.
        let num_peaks = (n + 1).ilog2();

        Self {
            n,
            current_i: num_peaks - 1,
            remaining: num_peaks,
            start_leaf_cursor: 0,
        }
    }

    /// Number of leaves in the MMB.
    pub(crate) const fn leaves(&self) -> u64 {
        self.n
    }

    /// Number of peaks not yet yielded.
    pub(crate) const fn remaining(&self) -> u32 {
        self.remaining
    }

    /// The next peak as `(position, height)`, or `None` after the newest.
    pub(crate) const fn next(&mut self) -> Option<(u64, u32)> {
        if self.remaining == 0 {
            return None;
        }

        let i = self.current_i;
        let n_val = self.n;

        // Height formula: h_i = i + b_i where b_i = ((n+1) >> i) & 1. Index `i` corresponds to the
        // original newest-to-oldest numbering; we iterate from the highest `i` (oldest) down to 0
        // (newest).
        let height = (i as u64) + (((n_val + 1) >> i) & 1);
        let leaves_in_peak = 1u64 << height;

        // The last leaf in this peak's subtree.
        let last_leaf = self.start_leaf_cursor + leaves_in_peak - 1;

        // Advance the cursor rightward for the next (newer) peak.
        self.start_leaf_cursor += leaves_in_peak;
        self.current_i = self.current_i.wrapping_sub(1);
        self.remaining -= 1;

        let n_birth = peak_birth_leaf(last_leaf, height as u32);
        Some((birthed_node_pos(n_birth, height == 0), height as u32))
    }
}

/// Compute the birth leaves of both children of a parent with the given birth leaf and height.
///
/// Returns `(left_leaf, right_leaf)`. The left child is always the older (lower leaf index) child.
pub(crate) const fn child_leaves(parent_leaf: u64, height: u32) -> (u64, u64) {
    if height == 1 {
        (parent_leaf - 1, parent_leaf)
    } else {
        let base = 1u64 << (height - 2);
        (parent_leaf - 3 * base, parent_leaf - base)
    }
}

/// Convert a leaf to the position of the node it births: the leaf itself if `is_leaf`, otherwise
/// the parent created alongside it.
///
/// A leaf created alongside `birth_leaf` has position `location_to_position(birth_leaf)`. A parent
/// created alongside `birth_leaf` has position `location_to_position(birth_leaf) + 1`.
///
/// # Warning
///
/// This calculates based solely on the structural math. If called with `is_leaf = false` on a
/// `birth_leaf` where no parent was actually birthed, it blindly returns the position of the next
/// appended leaf instead. It is the caller's responsibility to ensure a parent node functionally
/// exists at the provided `birth_leaf`.
pub(crate) const fn birthed_node_pos(birth_leaf: u64, is_leaf: bool) -> u64 {
    if is_leaf {
        location_to_position(birth_leaf)
    } else {
        location_to_position(birth_leaf) + 1
    }
}

/// Compute the birth leaf of a parent node from its position, or `None` if `pos` is not a parent.
///
/// A parent created alongside `birth_leaf` has position `location_to_position(birth_leaf) + 1`.
/// This function inverts that formula.
pub(crate) const fn parent_birth_leaf(pos: u64) -> Option<u64> {
    // The first parent in an MMB is always at index 2 (merging leaves 0 and 1).
    if pos < 2 {
        return None;
    }

    // Every position in an MMB is strictly either a leaf or a parent. A position on an MMB
    // footprint boundary is a leaf and must be rejected.
    if position_to_location(pos).is_some() {
        return None;
    }

    // A parent's position is exactly location_to_position(s) + 1, so `pos - 1` must be the
    // position of a leaf.
    position_to_location(pos - 1)
}

/// Compute the positions of the left and right children of a parent node.
///
/// Uses the delay matrix: for a parent at height h created at `birth_leaf`, its children (both at
/// height h-1) were created at leaves determined by fixed delays that depend only on h.
///
/// # Panics
///
/// Panics if `height` is 0 or if `pos` is not a valid parent position.
pub(crate) fn children(pos: u64, height: u32) -> (u64, u64) {
    assert!(height > 0, "height-0 nodes are leaves and have no children");

    let s = parent_birth_leaf(pos).expect("pos is not a valid parent position");

    let (left_leaf, right_leaf) = child_leaves(s, height);
    let is_leaf = height == 1;
    let left = birthed_node_pos(left_leaf, is_leaf);
    let right = birthed_node_pos(right_leaf, is_leaf);

    (left, right)
}

/// Compute the birth leaf of a peak from its last leaf and height.
///
/// For a height-0 peak (bare leaf), the birth leaf equals the last leaf index. For a taller peak,
/// the birth leaf is `last_leaf + 2^(h-1) - 1`.
pub(crate) const fn peak_birth_leaf(last_leaf: u64, height: u32) -> u64 {
    if height == 0 {
        last_leaf
    } else {
        last_leaf + (1u64 << (height - 1)) - 1
    }
}
