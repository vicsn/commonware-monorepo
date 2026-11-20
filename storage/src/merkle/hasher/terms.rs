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
pub(crate) const MAX_PARTS: usize = 4;

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
