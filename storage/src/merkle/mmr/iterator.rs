//! Iterators for traversing MMRs of a given size, and functions for computing various MMR
//! properties from their output. These are lower levels methods that are useful for implementing
//! new MMR variants or extensions.

use crate::merkle::{
    Family as _,
    mmr::{Family, Location, Position, geometry},
};

/// A PeakIterator returns a (position, height) tuple for each peak in an MMR with the given size,
/// in decreasing order of height.
///
/// For the example MMR depicted at the top of this file, the PeakIterator would yield:
/// ```text
/// [(14, 3), (17, 1), (18, 0)]
/// ```
#[derive(Default)]
pub struct PeakIterator(geometry::Peaks);

impl PeakIterator {
    /// Return a new PeakIterator over the peaks of a MMR with the given number of nodes.
    ///
    /// # Panics
    ///
    /// Panics if size is not a valid MMR size. If used on untrusted input, call
    /// `Position::is_valid_size` first.
    pub fn new(size: Position) -> Self {
        let leaves = Location::try_from(size).expect("size is not a valid MMR size");
        Self(geometry::Peaks::new(*leaves))
    }

    /// Returns the largest valid MMR size that is no greater than the given size.
    ///
    /// This is an O(log2(n)) operation using binary search on the number of leaves.
    ///
    /// # Panics
    ///
    /// Panics if `size` exceeds [Family::MAX_NODES].
    pub fn to_nearest_size(size: Position) -> Position {
        assert!(size <= Family::MAX_NODES, "size exceeds MAX_NODES");

        // Algorithm: A valid MMR size corresponds to a specific number of leaves N, where:
        // mmr_size(N) = 2*N - popcount(N)
        // This formula comes from the fact that N leaves require N-1 internal nodes, but merging
        // creates popcount(N)-1 additional nodes. We binary search for the largest N where
        // mmr_size(N) <= size.

        if size == 0 {
            return size;
        }

        // Binary search for the largest N (number of leaves) such that
        // mmr_size(N) = 2*N - popcount(N) <= size
        let size_val = size.as_u64();
        let mut low = 0u64;
        let mut high = size_val; // MMR size >= leaf count, so N <= size

        while low < high {
            // Use div_ceil for upper-biased midpoint in binary search
            let mid = (low + high).div_ceil(2);
            let mmr_size = 2 * mid - mid.count_ones() as u64;

            if mmr_size <= size_val {
                low = mid;
            } else {
                high = mid - 1;
            }
        }

        // low is the largest N where mmr_size(N) <= size
        let result = 2 * low - low.count_ones() as u64;
        Position::new(result)
    }
}

impl Iterator for PeakIterator {
    type Item = (Position, u32); // (peak, height)

    fn next(&mut self) -> Option<Self::Item> {
        self.0
            .next()
            .map(|(position, height)| (Position::new(position), height))
    }
}

/// Returns the height of the node at position `pos` in an MMR.
pub(crate) const fn pos_to_height(pos: Position) -> u32 {
    let mut pos = pos.as_u64();

    if pos == 0 {
        return 0;
    }

    let mut size = u64::MAX >> pos.leading_zeros();
    while size != 0 {
        if pos >= size {
            pos -= size;
        }
        size >>= 1;
    }

    pos as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The size-based peak search the leaf-count iterator replaced.
    fn reference_peaks(size: u64) -> Vec<(u64, u32)> {
        let mut peaks = Vec::new();
        if size == 0 {
            return peaks;
        }
        let start = u64::MAX >> size.leading_zeros();
        let mut two_h = 1u64 << start.trailing_ones();
        let mut node_pos = start - 1;
        while two_h > 1 {
            if node_pos < size {
                peaks.push((node_pos, two_h.trailing_zeros() - 1));
                node_pos += two_h - 1;
                continue;
            }
            two_h >>= 1;
            node_pos -= two_h;
        }
        peaks
    }

    #[test]
    fn peaks_match_reference() {
        let large = (0..64).flat_map(|shift| {
            let base = 1u64 << shift.min(62);
            [base - 1, base, base + 1, base | (base >> 1)]
        });
        for leaves in (0u64..=5000).chain(large) {
            if leaves > geometry::MAX_LEAVES {
                continue;
            }
            let size = Position::try_from(Location::new(leaves)).unwrap();
            let peaks: Vec<_> = PeakIterator::new(size)
                .map(|(position, height)| (*position, height))
                .collect();
            assert_eq!(peaks, reference_peaks(*size), "leaves={leaves}");
        }
    }
    use crate::merkle::{
        Bagging::ForwardFold,
        mmr::{Location, StandardHasher as Standard, mem::Mmr},
    };
    use commonware_cryptography::Sha256;

    #[test]
    fn test_leaf_loc_calculation() {
        // Build MMR with 1000 leaves and make sure we can correctly convert each leaf position to
        // its number and back again.
        let hasher = Standard::<Sha256>::new(ForwardFold);
        let mut mmr = Mmr::new();
        let digest = [1u8; 32];
        let (batch, loc_to_pos) = {
            let mut batch = mmr.new_batch();
            let mut positions = Vec::with_capacity(1000);
            for _ in 0..1000 {
                let loc = batch.leaves();
                batch = batch.add(&hasher, &digest);
                positions.push(Position::try_from(loc).unwrap());
            }
            (batch.merkleize(&mmr, &hasher), positions)
        };
        mmr.apply_batch(&batch).unwrap();

        let mut last_leaf_pos = 0;
        for (leaf_loc_expected, leaf_pos) in loc_to_pos.into_iter().enumerate() {
            let leaf_loc_got = Location::try_from(leaf_pos).unwrap();
            assert_eq!(leaf_loc_got, Location::new(leaf_loc_expected as u64));
            let leaf_pos_got = Position::try_from(leaf_loc_got).unwrap();
            assert_eq!(leaf_pos_got, *leaf_pos);
            for i in last_leaf_pos + 1..*leaf_pos {
                assert!(Location::try_from(Position::new(i)).is_err());
            }
            last_leaf_pos = *leaf_pos;
        }
    }

    #[test]
    #[should_panic(expected = "size exceeds MAX_NODES")]
    fn test_to_nearest_size_panic() {
        PeakIterator::to_nearest_size(Family::MAX_NODES + 1);
    }

    #[test]
    fn test_to_nearest_size() {
        // Build an MMR incrementally and verify to_nearest_size for all intermediate values
        let hasher = Standard::<Sha256>::new(ForwardFold);
        let mut mmr = Mmr::new();
        let digest = [1u8; 32];

        for _ in 0..1000 {
            let current_size = mmr.size();

            // Test positions from current size up to current size + 10
            for test_pos in *current_size..=*current_size + 10 {
                let rounded = PeakIterator::to_nearest_size(Position::new(test_pos));

                // Verify rounded is a valid MMR size
                assert!(
                    rounded.is_valid_size(),
                    "rounded size {rounded} should be valid (test_pos: {test_pos}, current: {current_size})",
                );

                // Verify rounded <= test_pos
                assert!(
                    rounded <= test_pos,
                    "rounded {rounded} should be <= test_pos {test_pos} (current: {current_size})",
                );

                // Verify rounded is the largest valid size <= test_pos
                if rounded < test_pos {
                    assert!(
                        !(rounded + 1).is_valid_size(),
                        "rounded {rounded} should be largest valid size <= {test_pos} (current: {current_size})",
                    );
                }
            }

            let batch = mmr
                .new_batch()
                .add(&hasher, &digest)
                .merkleize(&mmr, &hasher);
            mmr.apply_batch(&batch).unwrap();
        }
    }

    #[test]
    fn test_to_nearest_size_specific_cases() {
        // Test edge cases
        assert_eq!(PeakIterator::to_nearest_size(Position::new(0)), 0);
        assert_eq!(PeakIterator::to_nearest_size(Position::new(1)), 1);

        // Test consecutive values
        let mut expected = Position::new(0);
        for size in 0..=20 {
            let rounded = PeakIterator::to_nearest_size(Position::new(size));
            assert_eq!(rounded, expected);
            if Position::new(size + 1).is_valid_size() {
                expected = Position::new(size + 1);
            }
        }

        // Test with large value
        let large_size = Position::new(1_000_000);
        let rounded = PeakIterator::to_nearest_size(large_size);
        assert!(rounded.is_valid_size());
        assert!(rounded <= large_size);

        // Test maximum allowed input.
        let largest_valid_size = Family::MAX_NODES;
        let rounded = PeakIterator::to_nearest_size(largest_valid_size);
        assert!(rounded.is_valid_size());
        assert!(rounded <= largest_valid_size);
    }
}
