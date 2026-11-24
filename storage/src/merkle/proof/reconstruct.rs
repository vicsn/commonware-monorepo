//! Range-proof root reconstruction over abstract digests and peak geometry.
//!
//! [`Proof::reconstruct_root_inner`](super::Proof) and the current-database verifier call
//! [`reconstruct`]. It uses no Merkle types: the family supplies its peaks through [`Geometry`],
//! node digests through [`Nodes`] and hashing through [`Terms`], so the symbolic verification
//! extracts this file unchanged.

use super::traversal::{self, Collect, Nodes, Opening};
use crate::merkle::hasher::terms::{self, Cursor, Terms};

/// Why a range proof does not reconstruct a root.
pub(crate) enum Error {
    /// The proof carries more digests or elements than the range uses.
    ExtraDigests,
    /// The proof's inactive peak count does not fit its peaks.
    InvalidProof,
    /// Fewer elements than the range covers.
    MissingElements,
    /// The start location is not a valid leaf index.
    InvalidStartLoc,
    /// The range ends past the structure or the largest leaf count.
    InvalidEndLoc,
    /// The leaf count or the inactive peak count is not valid.
    InvalidSize,
    /// Fewer digests than the range needs.
    MissingDigests,
}

/// The peaks of one structure, oldest first.
pub(crate) trait Peaks {
    /// The next peak as `(position, height)`.
    fn next(&mut self) -> Option<(u64, u32)>;
}

/// The layout of the structures of one Merkle family.
pub(crate) trait Geometry {
    /// The peaks of one structure.
    type Peaks: Peaks;

    /// Domain tag the family commits in every root.
    fn domain(&self) -> u8;

    /// Largest valid leaf count.
    fn max_leaves(&self) -> u64;

    /// The peaks of a structure with `leaves <= max_leaves()` leaves.
    fn peaks(&self, leaves: u64) -> Self::Peaks;

    /// Positions of the two children of the node at `position`, whose subtree has `2^height`
    /// leaves.
    fn children(&self, position: u64, height: u32) -> (u64, u64);

    /// Number of leaves appended after the leftmost leaf of a node of `height` until the node
    /// exists.
    fn birth_offset(&self, height: u32) -> u64;
}

/// The nodes of family `G`, hashed with the standard leaf and node encodings of [`terms`].
pub(crate) struct StandardNodes<'a, G, T> {
    geometry: &'a G,
    terms: &'a T,
}

impl<'a, G, T> StandardNodes<'a, G, T> {
    /// Nodes laid out by `geometry` and hashed by `terms`.
    pub(crate) const fn new(geometry: &'a G, terms: &'a T) -> Self {
        Self { geometry, terms }
    }
}

impl<G: Geometry, T: Terms> Nodes for StandardNodes<'_, G, T> {
    type Digest = T::Digest;

    fn children(&self, position: u64, height: u32) -> (u64, u64) {
        self.geometry.children(position, height)
    }

    fn leaf_digest(&self, position: u64, element: &[u8]) -> T::Digest {
        terms::leaf_digest(self.terms, position, element)
    }

    fn node_digest(
        &self,
        position: u64,
        _height: u32,
        _start: u64,
        left: &T::Digest,
        right: &T::Digest,
    ) -> T::Digest {
        terms::node_digest(self.terms, position, left, right)
    }
}

/// An element of a range proof.
pub(crate) struct Element<'a>(&'a [u8]);

impl AsRef<[u8]> for Element<'_> {
    fn as_ref(&self) -> &[u8] {
        self.0
    }
}

/// The elements of a range proof of one element.
pub(crate) struct Single<'a>(Option<&'a [u8]>);

impl<'a> Single<'a> {
    /// Yield `element` once.
    pub(crate) const fn new(element: &'a [u8]) -> Self {
        Self(Some(element))
    }
}

impl<'a> Iterator for Single<'a> {
    type Item = Element<'a>;

    fn next(&mut self) -> Option<Element<'a>> {
        match self.0 {
            Some(element) => {
                self.0 = None;
                Some(Element(element))
            }
            None => None,
        }
    }
}

/// Reads a slice of digests from both ends.
pub(crate) struct Ends<'a, D> {
    digests: &'a [D],
    front: usize,
    back: usize,
}

impl<'a, D> Ends<'a, D> {
    /// Read all of `digests`.
    pub(crate) const fn new(digests: &'a [D]) -> Self {
        Self {
            digests,
            front: 0,
            back: digests.len(),
        }
    }
}

impl<D: Copy> Cursor for Ends<'_, D> {
    type Digest = D;

    fn next(&mut self) -> Option<D> {
        if self.front < self.back {
            let digest = self.digests[self.front];
            self.front += 1;
            Some(digest)
        } else {
            None
        }
    }

    fn next_back(&mut self) -> Option<D> {
        if self.front < self.back {
            self.back -= 1;
            Some(self.digests[self.back])
        } else {
            None
        }
    }
}

/// Number of sibling digests that rebuild a perfect subtree of `width` leaves starting at
/// `start` from the elements in `range_start..range_end`: one per maximal subtree outside it.
pub(crate) fn siblings(width: u64, start: u64, range_start: u64, range_end: u64) -> usize {
    if start + width <= range_start || start >= range_end {
        return 1;
    }
    if width == 1 {
        return 0;
    }
    let half = width / 2;
    siblings(half, start, range_start, range_end)
        + siblings(half, start + half, range_start, range_end)
}

/// How the peaks of a structure enter a range proof.
pub(crate) struct Layout {
    /// Peaks wholly before the range.
    pub(crate) before: usize,
    /// Peaks overlapping the range.
    pub(crate) overlapping: usize,
    /// Peaks wholly after the range.
    pub(crate) after: usize,
    /// Leading peaks folded into one prefix accumulator.
    pub(crate) fold: usize,
    /// Peaks after the range listed individually; the rest form one suffix accumulator.
    pub(crate) individual_after: usize,
}

impl Layout {
    /// Lay out `before`, `overlapping` and `after` peaks for a global boundary of `inactive`
    /// peaks, or `None` if `inactive` exceeds the number of peaks.
    ///
    /// Forward bagging folds every peak before the range into the prefix accumulator and lists
    /// every peak after it. Backward bagging folds only the inactive peaks before the range and
    /// collapses the active peaks after it into one suffix accumulator.
    pub(crate) const fn new(
        before: usize,
        overlapping: usize,
        after: usize,
        inactive: usize,
        backward: bool,
    ) -> Option<Self> {
        if inactive > before + overlapping + after {
            return None;
        }
        let (fold, individual_after) = if backward {
            let first_after = before + overlapping;
            let individual = inactive.saturating_sub(first_after);
            (
                if inactive < before { inactive } else { before },
                if individual < after {
                    individual
                } else {
                    after
                },
            )
        } else {
            (before, after)
        };
        Some(Self {
            before,
            overlapping,
            after,
            fold,
            individual_after,
        })
    }

    /// Number of prefix accumulators in the proof: one if any peak is folded.
    pub(crate) const fn fold_digests(&self) -> usize {
        if self.fold == 0 { 0 } else { 1 }
    }

    /// Number of suffix accumulators in the proof: one if any peak after the range is collapsed.
    pub(crate) const fn suffix_digests(&self) -> usize {
        if self.individual_after < self.after {
            1
        } else {
            0
        }
    }

    /// Index of the first individually listed peak before the range.
    pub(crate) const fn prefix_start(&self) -> usize {
        self.fold_digests()
    }

    /// Index of the first individually listed peak after the range.
    pub(crate) const fn after_start(&self) -> usize {
        self.prefix_start() + (self.before - self.fold)
    }

    /// Index of the suffix accumulator, if any.
    pub(crate) const fn suffix_start(&self) -> usize {
        self.after_start() + self.individual_after
    }

    /// Index of the first path sibling.
    pub(crate) const fn siblings_start(&self) -> usize {
        self.suffix_start() + self.suffix_digests()
    }

    /// Inactive peaks still to fold once the prefix accumulator replaces the folded peaks: the
    /// accumulator counts as one.
    pub(crate) const fn inactive_after_fold(&self, inactive: usize) -> usize {
        if self.fold == 0 {
            return inactive;
        }
        inactive.saturating_sub(self.fold) + 1
    }
}

/// Map a traversal failure to a reconstruction failure.
const fn missing(error: traversal::Error) -> Error {
    match error {
        traversal::Error::MissingElements => Error::MissingElements,
        traversal::Error::MissingDigests => Error::MissingDigests,
    }
}

/// Append the digest of every peak after the prefix accumulator and before the suffix
/// accumulator to `peak_digests`, oldest first, rebuilding the peaks that overlap
/// `start..end` with `opening` and recording each with its collector.
// The loop ends only in returns, which extraction requires.
#[allow(clippy::too_many_arguments)]
fn list_peaks<G, N, E, C>(
    geometry: &G,
    layout: &Layout,
    leaves: u64,
    digests: &[N::Digest],
    start: u64,
    end: u64,
    opening: &mut Opening<'_, N, E, C>,
    peak_digests: &mut Vec<N::Digest>,
) -> Result<(), Error>
where
    G: Geometry,
    N: Nodes,
    E: Iterator<Item: AsRef<[u8]>>,
    C: Collect<N::Digest>,
{
    let mut peaks = geometry.peaks(leaves);
    let mut index = 0;
    let mut leaf_start = 0u64;
    loop {
        let (position, height) = match peaks.next() {
            Some(peak) => peak,
            None => return Ok(()),
        };
        let width = 1u64 << height;
        if index < layout.before {
            if index >= layout.fold {
                let digest = digests[layout.prefix_start() + (index - layout.fold)];
                opening.peak(position, digest);
                peak_digests.push(digest);
            }
        } else if index < layout.before + layout.overlapping {
            let digest =
                match traversal::reconstruct(opening, position, width, leaf_start, start, end) {
                    Ok(digest) => digest,
                    Err(error) => return Err(missing(error)),
                };
            opening.peak(position, digest);
            peak_digests.push(digest);
        } else {
            let offset = index - layout.before - layout.overlapping;
            if offset < layout.individual_after {
                let digest = digests[layout.after_start() + offset];
                opening.peak(position, digest);
                peak_digests.push(digest);
            }
        }
        leaf_start += width;
        index += 1;
    }
}

/// Reconstruct the root of a structure of `leaves` leaves from a range proof of the `count`
/// elements starting at `start`, which `elements` yields in order.
///
/// `digests` is the proof's digest list: `[fold? | prefix peaks | after peaks | suffix? |
/// siblings]`, laid out by [`Layout`]. The root commits `domain` and folds with the bagging that
/// `backward` selects. `collected` receives every node and peak digest the reconstruction
/// authenticates, in order.
// Explicit matches keep fallible branches visible to extraction.
#[allow(
    clippy::option_if_let_else,
    clippy::question_mark,
    clippy::too_many_arguments
)]
pub(crate) fn reconstruct<G, T, N, E, C>(
    geometry: &G,
    terms: &T,
    nodes: N,
    domain: [u8; 2],
    backward: bool,
    leaves: u64,
    inactive: usize,
    digests: &[T::Digest],
    start: u64,
    count: u64,
    elements: E,
    collected: C,
) -> Result<T::Digest, Error>
where
    G: Geometry,
    T: Terms,
    N: Nodes<Digest = T::Digest>,
    E: Iterator<Item: AsRef<[u8]>>,
    C: Collect<T::Digest>,
{
    let mut elements = elements;
    let max_leaves = geometry.max_leaves();
    if count == 0 {
        if elements.next().is_some() {
            return Err(Error::ExtraDigests);
        }
        if start == 0 {
            if inactive != 0 {
                return Err(Error::InvalidProof);
            }
            if leaves != 0 {
                return Err(Error::MissingElements);
            }
            if digests.is_empty() {
                return Ok(terms::empty_root(terms, domain, leaves));
            }
            return Err(Error::ExtraDigests);
        }
        return Err(Error::MissingElements);
    }
    if start >= max_leaves {
        return Err(Error::InvalidStartLoc);
    }
    if count > max_leaves - start {
        return Err(Error::InvalidEndLoc);
    }
    let end = start + count;
    if end > leaves {
        return Err(Error::InvalidEndLoc);
    }
    if leaves > max_leaves {
        return Err(Error::InvalidSize);
    }

    // Classify the peaks by their leaf spans: before, overlapping or after the range.
    let mut peaks = geometry.peaks(leaves);
    let mut before = 0;
    let mut overlapping = 0;
    let mut after = 0;
    let mut path_siblings = 0;
    let mut leaf_start = 0u64;
    while let Some((_, height)) = peaks.next() {
        let width = 1u64 << height;
        let leaf_end = leaf_start + width;
        if leaf_end <= start {
            before += 1;
        } else if leaf_start >= end {
            after += 1;
        } else {
            overlapping += 1;
            path_siblings += siblings(width, leaf_start, start, end);
        }
        leaf_start = leaf_end;
    }
    let layout = match Layout::new(before, overlapping, after, inactive, backward) {
        Some(layout) => layout,
        None => return Err(Error::InvalidSize),
    };
    let first_sibling = layout.siblings_start();
    let required = first_sibling + path_siblings;
    if digests.len() < required {
        return Err(Error::MissingDigests);
    }
    if digests.len() > required {
        return Err(Error::ExtraDigests);
    }

    // List the peak digests in order, rebuilding the overlapping peaks from the elements and the
    // path siblings.
    let mut peak_digests = Vec::new();
    if layout.fold_digests() == 1 {
        peak_digests.push(digests[0]);
    }
    let mut opening = Opening::new(nodes, elements, digests, first_sibling, collected);
    if let Err(error) = list_peaks(
        geometry,
        &layout,
        leaves,
        digests,
        start,
        end,
        &mut opening,
        &mut peak_digests,
    ) {
        return Err(error);
    }
    if layout.suffix_digests() == 1 {
        peak_digests.push(digests[layout.suffix_start()]);
    }
    if !opening.exhausted() {
        return Err(Error::ExtraDigests);
    }
    if opening.cursor() != digests.len() {
        return Err(Error::ExtraDigests);
    }
    match terms::bagged_root(
        terms,
        domain,
        backward,
        leaves,
        layout.inactive_after_fold(inactive),
        inactive as u64,
        &mut Ends::new(&peak_digests),
    ) {
        Some(root) => Ok(root),
        None => Err(Error::InvalidProof),
    }
}
