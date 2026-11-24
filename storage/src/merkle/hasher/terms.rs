//! Hash inputs of Merkle-family digests, built over abstract terms.
//!
//! Every digest is the hash of a short sequence of parts, each either raw bytes or another
//! digest. The functions here fix those sequences once. [`Hasher`](super::Hasher) hashes the
//! concatenated bytes. A symbolic model can instead read hashing and concatenation as free
//! constructors, so proofs about code that builds digests through [`Terms`] apply unchanged.

/// One part of a hash input.
pub(crate) enum Part<'a, D> {
    /// Raw bytes.
    Bytes(&'a [u8]),
    /// A digest.
    Digest(&'a D),
}

/// Digests of hash inputs given as parts.
pub(crate) trait Terms {
    /// Digest produced by hashing.
    type Digest: Copy + PartialEq;

    /// The digest of the concatenation of `parts`, which holds at most [`MAX_PARTS`] parts.
    fn hash(&self, parts: &[Part<'_, Self::Digest>]) -> Self::Digest;
}

/// Largest number of parts in any hash input built here.
pub(crate) const MAX_PARTS: usize = 5;

/// Leaf digest: `Hash(position || element)`, with the position as a big-endian `u64`.
pub(crate) fn leaf_digest<T: Terms>(terms: &T, position: u64, element: &[u8]) -> T::Digest {
    terms.hash(&[Part::Bytes(&position.to_be_bytes()), Part::Bytes(element)])
}

/// Node digest: `Hash(position || left || right)`, with the position as a big-endian `u64`.
pub(crate) fn node_digest<T: Terms>(
    terms: &T,
    position: u64,
    left: &T::Digest,
    right: &T::Digest,
) -> T::Digest {
    terms.hash(&[
        Part::Bytes(&position.to_be_bytes()),
        Part::Digest(left),
        Part::Digest(right),
    ])
}

/// Peak fold: `Hash(acc || peak)`.
pub(crate) fn fold<T: Terms>(terms: &T, acc: &T::Digest, peak: &T::Digest) -> T::Digest {
    terms.hash(&[Part::Digest(acc), Part::Digest(peak)])
}

/// Root: `Hash(domain || leaves [|| inactive] || folded)`, with `leaves` and `inactive` as
/// big-endian `u64`s and `inactive` present only when nonzero.
pub(crate) fn root<T: Terms>(
    terms: &T,
    domain: [u8; 2],
    leaves: u64,
    inactive: u64,
    folded: &T::Digest,
) -> T::Digest {
    if inactive == 0 {
        terms.hash(&[
            Part::Bytes(&domain),
            Part::Bytes(&leaves.to_be_bytes()),
            Part::Digest(folded),
        ])
    } else {
        terms.hash(&[
            Part::Bytes(&domain),
            Part::Bytes(&leaves.to_be_bytes()),
            Part::Bytes(&inactive.to_be_bytes()),
            Part::Digest(folded),
        ])
    }
}

/// Root of a structure without peaks: `Hash(domain || leaves)`.
pub(crate) fn empty_root<T: Terms>(terms: &T, domain: [u8; 2], leaves: u64) -> T::Digest {
    terms.hash(&[Part::Bytes(&domain), Part::Bytes(&leaves.to_be_bytes())])
}

/// Peak digests read from the oldest end with `next` and from the newest end with `next_back`.
pub(crate) trait Cursor {
    /// A peak digest.
    type Digest;

    /// The oldest unread peak digest.
    fn next(&mut self) -> Option<Self::Digest>;

    /// The newest unread peak digest.
    fn next_back(&mut self) -> Option<Self::Digest>;
}

/// Fold the oldest peaks into `first` until `to_fold` peaks (at least one) are folded, or `None`
/// if too few remain.
// The loop ends only in returns, which extraction requires.
fn fold_prefix<T: Terms, C: Cursor<Digest = T::Digest>>(
    terms: &T,
    first: T::Digest,
    to_fold: usize,
    peaks: &mut C,
) -> Option<T::Digest> {
    let mut acc = first;
    let mut folded = 1;
    loop {
        if folded >= to_fold {
            return Some(acc);
        }
        match peaks.next() {
            Some(peak) => {
                acc = fold(terms, &acc, &peak);
                folded += 1;
            }
            None => return None,
        }
    }
}

/// Root of the peaks in `peaks`, or `None` if `to_fold` exceeds their number or an empty
/// structure has a nonzero inactive boundary.
///
/// The first `to_fold` peaks (at least one) are folded oldest first into an accumulator. Forward
/// bagging folds the remaining peaks into it in the same order. Backward bagging folds them from the
/// newest, `Hash(peak || bag)`, and folds the result into the accumulator. `committed` is the
/// inactive boundary committed by [`root`]. Without peaks the root is [`empty_root`].
// Explicit matches keep fallible branches visible to extraction.
#[allow(clippy::option_if_let_else, clippy::question_mark)]
pub(crate) fn bagged_root<T: Terms, C: Cursor<Digest = T::Digest>>(
    terms: &T,
    domain: [u8; 2],
    backward: bool,
    leaves: u64,
    to_fold: usize,
    committed: u64,
    peaks: &mut C,
) -> Option<T::Digest> {
    let first = match peaks.next() {
        Some(first) => first,
        None => {
            if to_fold == 0 && committed == 0 {
                return Some(empty_root(terms, domain, leaves));
            }
            return None;
        }
    };
    let mut acc = match fold_prefix(terms, first, to_fold, peaks) {
        Some(acc) => acc,
        None => return None,
    };
    let bag = if backward {
        match peaks.next_back() {
            None => acc,
            Some(last) => {
                let mut bag = last;
                while let Some(peak) = peaks.next_back() {
                    bag = fold(terms, &peak, &bag);
                }
                fold(terms, &acc, &bag)
            }
        }
    } else {
        while let Some(peak) = peaks.next() {
            acc = fold(terms, &acc, &peak);
        }
        acc
    };
    Some(root(terms, domain, leaves, committed, &bag))
}

/// Canonical current root, including optional pending and partial bitmap chunk digests.
#[cfg(feature = "std")]
pub(crate) fn current_root<T: Terms>(
    terms: &T,
    ops: &T::Digest,
    grafted: &T::Digest,
    pending: Option<&T::Digest>,
    partial: Option<(u64, &T::Digest)>,
) -> T::Digest {
    let (ops, grafted) = (Part::Digest(ops), Part::Digest(grafted));
    match (pending, partial) {
        (None, None) => terms.hash(&[ops, grafted]),
        (Some(p), None) => terms.hash(&[ops, grafted, Part::Digest(p)]),
        (None, Some((next, d))) => terms.hash(&[
            ops,
            grafted,
            Part::Bytes(&next.to_be_bytes()),
            Part::Digest(d),
        ]),
        (Some(p), Some((next, d))) => terms.hash(&[
            ops,
            grafted,
            Part::Digest(p),
            Part::Bytes(&next.to_be_bytes()),
            Part::Digest(d),
        ]),
    }
}
