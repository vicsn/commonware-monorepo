//! Iterators for traversing MMBs of a given size, and functions for computing various MMB
//! properties from their output.

use crate::merkle::{
    Family as _,
    mmb::{Family, Location, Position, geometry},
};

/// A PeakIterator yields `(position, height)` for each peak in an MMB with the given size, in
/// order from **oldest** (leftmost) to **newest** (rightmost). Heights are always non-increasing.
///
/// The number of peaks after N leaves is always exactly `ilog2(N+1)`, and their heights are
/// non-increasing in this iteration order.
///
/// # Physical index ordering
///
/// The returned peaks are NOT monotonically ordered by position. This is due to the delayed
/// merging property of the MMB. A parent node at height `h` is not written immediately after its
/// leaves; instead, its creation is delayed by `2^(h-1) - 1` steps to maintain a constant rate of 1
/// merge per leaf.
///
/// As a result, older, taller peaks may be appended to the MMB *after* newer, shorter
/// peaks. For example, at `N=11` leaves, the Iterator yields peaks at positions `[18, 16, 17]`:
/// - `18`: The oldest height-3 peak (its merge was delayed by 3 steps).
/// - `16`: A height-1 peak (appended at step 9).
/// - `17`: The newest height-0 peak (a bare leaf added at step 10).
///
/// Code iterating through peaks must not assume their positions are sorted in any direction.
#[derive(Default)]
pub struct PeakIterator(geometry::Peaks);

impl PeakIterator {
    /// Return a new PeakIterator over the peaks of an MMB with the given number of nodes.
    ///
    /// # Panics
    ///
    /// Panics if size is not a valid MMB size.
    pub fn new(size: Position) -> Self {
        let n = Location::try_from(size).expect("size is not a valid MMB size");
        Self(geometry::Peaks::new(*n))
    }

    /// Return the number of leaves in the MMB.
    #[inline]
    pub const fn leaves(&self) -> Location {
        Location::new(self.0.leaves())
    }

    /// Returns the largest valid MMB size that is no greater than the given size.
    ///
    /// # Panics
    ///
    /// Panics if `size` exceeds [crate::merkle::Family::MAX_NODES].
    pub fn to_nearest_size(size: Position) -> Position {
        assert!(size <= Family::MAX_NODES, "size exceeds MAX_NODES");

        if size.as_u64() == 0 {
            return size;
        }

        // Use an O(1) estimate to find the baseline leaf count, then check if n+1
        // fits within the size boundary. location_to_position is monotonic, so one
        // refinement step from the estimate always suffices.
        let s = size.as_u64();
        let mut n = s / 2;
        n = (s + (n + 1).ilog2() as u64) / 2;

        let candidate = Family::location_to_position(Location::new(n + 1));
        if *candidate <= s {
            candidate
        } else {
            Family::location_to_position(Location::new(n))
        }
    }
}

impl Iterator for PeakIterator {
    type Item = (Position, u32); // (position, height)

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.0.remaining() as usize;
        (len, Some(len))
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.0
            .next()
            .map(|(position, height)| (Position::new(position), height))
    }
}

impl ExactSizeIterator for PeakIterator {}

/// Compute the positions of the left and right children of a parent node.
///
/// # Panics
///
/// Panics if `height` is 0 or if `pos` is not a valid parent position.
pub(crate) fn children(pos: Position, height: u32) -> (Position, Position) {
    let (left, right) = geometry::children(*pos, height);
    (Position::new(left), Position::new(right))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn child_leaves(parent_leaf: Location, height: u32) -> (Location, Location) {
        let (left, right) = geometry::child_leaves(*parent_leaf, height);
        (Location::new(left), Location::new(right))
    }

    fn birthed_node_pos(birth_leaf: Location, is_leaf: bool) -> Position {
        Position::new(geometry::birthed_node_pos(*birth_leaf, is_leaf))
    }

    fn parent_birth_leaf(pos: Position) -> Option<Location> {
        geometry::parent_birth_leaf(*pos).map(Location::new)
    }

    fn peak_birth_leaf(last_leaf: Location, height: u32) -> Location {
        Location::new(geometry::peak_birth_leaf(*last_leaf, height))
    }

    #[test]
    fn test_location_to_position() {
        assert_eq!(Family::location_to_position(Location::new(1)).as_u64(), 1);
        assert_eq!(Family::location_to_position(Location::new(2)).as_u64(), 3);
        assert_eq!(Family::location_to_position(Location::new(3)).as_u64(), 4);
        assert_eq!(Family::location_to_position(Location::new(4)).as_u64(), 6);
    }

    #[test]
    fn test_position_to_location_roundtrip() {
        for n in 1u64..=1000 {
            let size = Family::location_to_position(Location::new(n));
            assert_eq!(
                Family::position_to_location(size),
                Some(Location::new(n)),
                "N={n}"
            );
        }
    }

    #[test]
    fn test_max_position_and_max_location_consistent() {
        let max_pos = Family::MAX_NODES.as_u64();
        let max_loc = Family::MAX_LEAVES.as_u64();

        // MAX_NODES should correspond to MAX_LEAVES leaves.
        assert_eq!(
            Location::try_from(Position::new(max_pos)).ok(),
            Some(Location::new(max_loc)),
            "MAX_NODES should correspond to MAX_LEAVES leaves"
        );

        // The size formula should agree.
        assert_eq!(
            Position::try_from(Location::new(max_loc)).unwrap().as_u64(),
            max_pos,
            "location_to_position(MAX_LEAVES) should equal MAX_NODES"
        );

        // One more leaf should exceed MAX_NODES.
        let over_size = *Family::location_to_position(Location::new(max_loc + 1));
        assert!(over_size > max_pos, "one more leaf should exceed MAX_NODES");

        // Sizes above MAX_NODES should be rejected.
        assert!(!Position::new(max_pos + 1).is_valid());
    }

    #[test]
    fn test_child_leaves_matches_children() {
        for n in 1u64..=256 {
            let size = Position::try_from(Location::new(n)).unwrap();
            for (pos, height) in PeakIterator::new(size) {
                if height == 0 {
                    continue;
                }
                let leaf = parent_birth_leaf(pos).unwrap();
                let (left_leaf, right_leaf) = child_leaves(leaf, height);
                let is_leaf = height == 1;
                let left_pos = birthed_node_pos(left_leaf, is_leaf);
                let right_pos = birthed_node_pos(right_leaf, is_leaf);
                let (expected_left, expected_right) = children(pos, height);
                assert_eq!(
                    (left_pos, right_pos),
                    (expected_left, expected_right),
                    "n={n}, pos={pos}, height={height}"
                );
            }
        }
    }

    #[test]
    fn test_birthed_node_pos() {
        // Verify birthed_node_pos matches PeakIterator output for all peaks.
        for n in 1u64..=256 {
            let size = Position::try_from(Location::new(n)).unwrap();
            let mut first_leaf = 0u64;
            for (pos, height) in PeakIterator::new(size) {
                let leaves_in_peak = 1u64 << height;
                let last_leaf = first_leaf + leaves_in_peak - 1;
                let leaf = peak_birth_leaf(Location::new(last_leaf), height);
                let computed_pos = birthed_node_pos(leaf, height == 0);
                assert_eq!(computed_pos, pos, "n={n}, height={height}");
                first_leaf += leaves_in_peak;
            }
        }
    }

    #[test]
    fn test_invalid_sizes_rejected() {
        // Sizes between valid MMB sizes should fail conversion.
        for n in 1u64..=500 {
            let valid = *Position::try_from(Location::new(n)).unwrap();
            let next_valid = *Position::try_from(Location::new(n + 1)).unwrap();
            for gap in (valid + 1)..next_valid {
                assert!(
                    Location::try_from(Position::new(gap)).is_err(),
                    "size={gap} (between n={n} and n={}) should be invalid",
                    n + 1
                );
            }
        }
    }

    #[test]
    fn test_location_position_roundtrip() {
        use crate::merkle::mmb::{Location, Position};
        use core::convert::TryFrom;

        for n in 0u64..=1000 {
            let loc = Location::new(n);
            let pos = Position::try_from(loc).unwrap();

            // Roundtrip back to location.
            let loc2 = Location::try_from(pos).unwrap();
            assert_eq!(loc, loc2, "roundtrip failed for leaf {n}");

            // Non-leaf positions between consecutive leaves should fail.
            if n > 0 {
                let prev_loc = Location::new(n - 1);
                let prev_pos = Position::try_from(prev_loc).unwrap();
                for gap_pos in (*prev_pos + 1)..*pos {
                    assert!(
                        Location::try_from(Position::new(gap_pos)).is_err(),
                        "position {gap_pos} between leaves {prev_pos} and {pos} should not be a leaf"
                    );
                }
            }
        }
    }

    #[test]
    fn test_parent_birth_leaf_rejects_leaf_positions() {
        // These are valid leaf positions that previously slipped through the simplified
        // `parent_birth_leaf` check because `pos - 1` is also a valid MMB size.
        assert_eq!(parent_birth_leaf(Position::new(4)), None);
        assert_eq!(parent_birth_leaf(Position::new(11)), None);
    }

    #[test]
    #[should_panic(expected = "pos is not a valid parent position")]
    fn test_children_rejects_leaf_position() {
        children(Position::new(4), 1);
    }

    #[test]
    fn test_peak_birth_leaf() {
        // Verify peak_birth_leaf matches the inline computation used in test_birthed_node_pos.
        for n in 1u64..=256 {
            let size = Position::try_from(Location::new(n)).unwrap();
            let mut first_leaf = 0u64;
            for (pos, height) in PeakIterator::new(size) {
                let leaves_in_peak = 1u64 << height;
                let last_leaf = first_leaf + leaves_in_peak - 1;
                let leaf = peak_birth_leaf(Location::new(last_leaf), height);
                let computed_pos = birthed_node_pos(leaf, height == 0);
                assert_eq!(computed_pos, pos, "n={n}, height={height}");
                first_leaf += leaves_in_peak;
            }
        }
    }

    #[test]
    fn test_to_nearest_size() {
        // Zero maps to zero.
        assert_eq!(
            PeakIterator::to_nearest_size(Position::new(0)),
            Position::new(0)
        );

        // For every size 0..2000: result is valid, <= input, monotonic, and exact sizes
        // are unchanged while gaps round down.
        let mut prev = Position::new(0);
        for s in 0u64..=2000 {
            let nearest = PeakIterator::to_nearest_size(Position::new(s));
            assert!(
                nearest.is_valid_size(),
                "result {nearest} not valid for input {s}"
            );
            assert!(
                nearest <= Position::new(s),
                "result {nearest} exceeds input {s}"
            );
            assert!(nearest >= prev, "not monotonic at {s}");
            prev = nearest;
        }

        // Valid sizes map to themselves; gaps map to the previous valid size.
        for n in 1u64..=500 {
            let size = Position::try_from(Location::new(n)).unwrap();
            assert_eq!(PeakIterator::to_nearest_size(size), size, "n={n}");

            let next_size = Position::try_from(Location::new(n + 1)).unwrap();
            for s in *size + 1..*next_size {
                assert_eq!(
                    PeakIterator::to_nearest_size(Position::new(s)),
                    size,
                    "gap size {s} between n={n} and n={}",
                    n + 1
                );
            }
        }
    }
}
