//! Verification of current range and operation proofs over abstract digests.
//!
//! [`RangeProof`](super::RangeProof) and [`OperationProof`](super::operation::Proof) verify through
//! these functions. They use no Merkle types: the ops tree's family supplies its layout through
//! [`Geometry`] and hashing goes through [`Terms`], so the symbolic verification extracts this file
//! unchanged.

use super::activity;
use crate::{
    merkle::{
        hasher::terms::{self, Terms},
        proof::{
            reconstruct::{self, Geometry, Single, StandardNodes},
            traversal::Collect,
        },
    },
    qmdb::current::grafting::rules::{self as grafting, Grafted},
};

/// Bits in a bitmap chunk of `chunk_size` bytes, or `None` unless the bit width is a power of two
/// below `2^63`.
pub(crate) const fn chunk_bits(chunk_size: usize) -> Option<u64> {
    if chunk_size > usize::MAX / 8 {
        return None;
    }
    let bits = (chunk_size * 8) as u64;
    if bits == 0 || bits & (bits - 1) != 0 || bits > 1 << 62 {
        return None;
    }
    Some(bits)
}

/// Whether every chunk in `chunks` holds `chunk_size` bytes.
// The loop ends only in returns, which extraction requires.
fn sized<C: AsRef<[u8]>>(chunks: &[C], chunk_size: usize) -> bool {
    let mut index = 0;
    loop {
        if index == chunks.len() {
            return true;
        }
        if chunks[index].as_ref().len() != chunk_size {
            return false;
        }
        index += 1;
    }
}

/// The fields of a current range proof.
pub(crate) struct Fields<'a, D> {
    /// Leaves of the ops tree.
    pub(crate) leaves: u64,
    /// Inactive peaks of the ops tree.
    pub(crate) inactive: usize,
    /// The ops-tree range proof's digests.
    pub(crate) digests: &'a [D],
    /// Root of the ops tree.
    pub(crate) ops_root: D,
    /// Digest of the complete chunk whose ancestor is not yet born, if any.
    pub(crate) pending: Option<D>,
    /// Digest of the trailing partial chunk, if any.
    pub(crate) partial: Option<D>,
}

/// Whether the `count` operations from `start` lie in a structure of `leaves <= max_leaves`
/// leaves and `chunks` holds exactly the chunks of `bits` bits covering them, each of
/// `chunk_size` bytes.
fn covered<C: AsRef<[u8]>>(
    max_leaves: u64,
    leaves: u64,
    start: u64,
    count: u64,
    bits: u64,
    chunks: &[C],
    chunk_size: usize,
) -> bool {
    if count == 0 || chunks.is_empty() {
        return false;
    }
    if count > max_leaves || start > max_leaves - count {
        return false;
    }
    let end = start + count;
    if end > leaves {
        return false;
    }
    if (end - 1) / bits - start / bits + 1 != chunks.len() as u64 {
        return false;
    }
    sized(chunks, chunk_size)
}

/// The smaller of `a` and `b`.
const fn smaller(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}

/// Whether the proof carries a partial chunk digest exactly when the bitmap ends `next_bit` bits
/// into a chunk, and that digest is the digest of the last supplied chunk when the range reaches
/// it.
fn partial_matches<T: Terms, C: AsRef<[u8]>>(
    terms: &T,
    partial: Option<T::Digest>,
    next_bit: u64,
    end_chunk: u64,
    complete: u64,
    chunks: &[C],
) -> bool {
    match partial {
        None => next_bit == 0,
        Some(partial) => {
            if next_bit == 0 {
                return false;
            }
            if end_chunk != complete {
                return true;
            }
            partial == grafting::chunk_digest(terms, chunks[chunks.len() - 1].as_ref())
        }
    }
}

/// Whether the proof carries a pending chunk digest exactly when `complete - graftable == 1`, and
/// that digest is the digest of the pending chunk when the range covers it.
fn pending_matches<T: Terms, C: AsRef<[u8]>>(
    terms: &T,
    pending: Option<T::Digest>,
    graftable: u64,
    complete: u64,
    start_chunk: u64,
    end_chunk: u64,
    chunks: &[C],
) -> bool {
    match pending {
        None => complete - graftable != 1,
        Some(pending) => {
            if complete - graftable != 1 {
                return false;
            }
            if graftable < start_chunk || graftable > end_chunk {
                return true;
            }
            let local = (graftable - start_chunk) as usize;
            if local >= chunks.len() {
                return false;
            }
            pending == grafting::chunk_digest(terms, chunks[local].as_ref())
        }
    }
}

/// The canonical current root over `merkle` and the proof's suffix digests; the partial chunk
/// enters with its first unused bit `next_bit`.
fn canonical<T: Terms>(
    terms: &T,
    proof: &Fields<'_, T::Digest>,
    merkle: &T::Digest,
    next_bit: u64,
) -> T::Digest {
    match (proof.pending, proof.partial) {
        (Some(pending), Some(partial)) => terms::current_root(
            terms,
            &proof.ops_root,
            merkle,
            Some(&pending),
            Some((next_bit, &partial)),
        ),
        (Some(pending), None) => {
            terms::current_root(terms, &proof.ops_root, merkle, Some(&pending), None)
        }
        (None, Some(partial)) => terms::current_root(
            terms,
            &proof.ops_root,
            merkle,
            None,
            Some((next_bit, &partial)),
        ),
        (None, None) => terms::current_root(terms, &proof.ops_root, merkle, None, None),
    }
}

/// Reconstruct the canonical current root from a range proof of the `count` operations starting
/// at `start`, which `elements` yields encoded, and the bitmap `chunks` covering them.
///
/// The ops tree is laid out by `geometry`, and its roots fold with the bagging that `backward`
/// selects and commit `bagging_domain`. `collected` receives the digests that reconstruction
/// authenticates.
// Explicit matches keep fallible branches visible to extraction.
#[allow(
    clippy::option_if_let_else,
    clippy::question_mark,
    clippy::too_many_arguments
)]
pub(crate) fn reconstruct<G, T, E, C, R>(
    geometry: &G,
    terms: &T,
    bagging_domain: u8,
    backward: bool,
    proof: &Fields<'_, T::Digest>,
    start: u64,
    count: u64,
    elements: E,
    chunks: &[C],
    chunk_size: usize,
    collected: R,
) -> Option<T::Digest>
where
    G: Geometry,
    T: Terms,
    E: Iterator<Item: AsRef<[u8]>>,
    C: AsRef<[u8]>,
    R: Collect<T::Digest>,
{
    let bits = match chunk_bits(chunk_size) {
        Some(bits) => bits,
        None => return None,
    };
    let leaves = proof.leaves;
    if !covered(
        geometry.max_leaves(),
        leaves,
        start,
        count,
        bits,
        chunks,
        chunk_size,
    ) {
        return None;
    }
    let start_chunk = start / bits;
    let end_chunk = (start + count - 1) / bits;
    let complete = leaves / bits;
    let next_bit = leaves % bits;
    let grafting_height = bits.ilog2();

    // At most one complete chunk awaits its ancestor; the proof carries its digest exactly when it
    // exists and the bitmap's trailing partial chunk exactly when there is one.
    let born = grafting::graftable_chunks(
        leaves,
        grafting_height,
        geometry.birth_offset(grafting_height),
    );
    let graftable = smaller(born, complete);
    if complete - graftable > 1 {
        return None;
    }
    if !partial_matches(terms, proof.partial, next_bit, end_chunk, complete, chunks) {
        return None;
    }
    if !pending_matches(
        terms,
        proof.pending,
        graftable,
        complete,
        start_chunk,
        end_chunk,
        chunks,
    ) {
        return None;
    }

    let nodes = Grafted::new(
        StandardNodes::new(geometry, terms),
        terms,
        grafting_height,
        start_chunk,
        chunks,
        graftable,
    );
    match reconstruct::reconstruct(
        geometry,
        terms,
        nodes,
        [geometry.domain(), bagging_domain],
        backward,
        leaves,
        proof.inactive,
        proof.digests,
        start,
        count,
        elements,
        collected,
    ) {
        Ok(merkle) => Some(canonical(terms, proof, &merkle, next_bit)),
        Err(_) => None,
    }
}

/// A bitmap chunk supplied to [`reconstruct`].
struct Chunk<'a>(&'a [u8]);

impl AsRef<[u8]> for Chunk<'_> {
    fn as_ref(&self) -> &[u8] {
        self.0
    }
}

/// Whether the proof `proof` with bitmap chunk `chunk` authenticates `element`, an encoded
/// operation, as active at location `location` under the canonical current root `root`.
// Explicit matches keep fallible branches visible to extraction.
#[allow(clippy::option_if_let_else, clippy::too_many_arguments)]
pub(crate) fn verify_operation<G: Geometry, T: Terms>(
    geometry: &G,
    terms: &T,
    bagging_domain: u8,
    backward: bool,
    proof: &Fields<'_, T::Digest>,
    location: u64,
    chunk: &[u8],
    element: &[u8],
    root: &T::Digest,
) -> bool {
    let bits = match chunk_bits(chunk.len()) {
        Some(bits) => bits,
        None => return false,
    };
    if !activity::get(chunk, location, bits) {
        return false;
    }
    match reconstruct(
        geometry,
        terms,
        bagging_domain,
        backward,
        proof,
        location,
        1,
        Single::new(element),
        &[Chunk(chunk)],
        chunk.len(),
        (),
    ) {
        Some(reconstructed) => reconstructed == *root,
        None => false,
    }
}
