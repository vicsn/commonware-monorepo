//! Grafted node digests and graftable chunk counts over abstract digests.
//!
//! [`super::Verifier`], [`super::graftable_chunks`] and the current-proof verifier call these
//! functions. They use no Merkle types, so the symbolic verification extracts this file unchanged.

use crate::merkle::{
    hasher::terms::{Part, Terms},
    proof::traversal::Nodes,
};

/// Number of bitmap chunks whose ops-tree ancestor at `grafting_height` exists after `leaves`
/// leaves, when the first such ancestor is born at leaf count `first_birth`.
pub(crate) const fn graftable_chunks(leaves: u64, grafting_height: u32, first_birth: u64) -> u64 {
    if leaves < first_birth {
        return 0;
    }
    (leaves - first_birth) / (1u64 << grafting_height) + 1
}

/// Whether every byte of `chunk` is zero.
// The loop ends only in returns, which extraction requires.
pub(crate) fn is_zero(chunk: &[u8]) -> bool {
    let mut index = 0;
    loop {
        if index == chunk.len() {
            return true;
        }
        if chunk[index] != 0 {
            return false;
        }
        index += 1;
    }
}

/// Digest of a bitmap chunk: `Hash(chunk)`.
pub(crate) fn chunk_digest<T: Terms>(terms: &T, chunk: &[u8]) -> T::Digest {
    terms.hash(&[Part::Bytes(chunk)])
}

/// Grafted leaf of `chunk` over the ops subtree root `subtree`: the root itself for an all-zero
/// chunk, otherwise `Hash(chunk || subtree)`.
pub(crate) fn grafted_leaf<T: Terms>(terms: &T, chunk: &[u8], subtree: T::Digest) -> T::Digest {
    if is_zero(chunk) {
        subtree
    } else {
        terms.hash(&[Part::Bytes(chunk), Part::Digest(&subtree)])
    }
}

/// Graft the ops-tree node `node`, whose subtree starts at leaf `start`, at the grafting height.
///
/// The node covers chunk `start >> grafting_height`. A chunk at or beyond `graftable` is pending
/// and leaves the node unchanged, as does a chunk outside `chunks`, which holds the chunks from
/// index `start_chunk`. Otherwise the node becomes the [`grafted_leaf`] of its chunk.
pub(crate) fn graft<T: Terms, C: AsRef<[u8]>>(
    terms: &T,
    grafting_height: u32,
    start_chunk: u64,
    chunks: &[C],
    graftable: u64,
    start: u64,
    node: T::Digest,
) -> T::Digest {
    let chunk = start >> grafting_height;
    if chunk >= graftable || chunk < start_chunk {
        return node;
    }
    let local = chunk - start_chunk;
    if local >= chunks.len() as u64 {
        return node;
    }
    grafted_leaf(terms, chunks[local as usize].as_ref(), node)
}

/// The nodes of an ops tree whose nodes at the grafting height are grafted with bitmap chunks.
pub(crate) struct Grafted<'a, N, T, C> {
    nodes: N,
    terms: &'a T,
    grafting_height: u32,
    start_chunk: u64,
    chunks: &'a [C],
    graftable: u64,
}

impl<'a, N, T, C> Grafted<'a, N, T, C> {
    /// Graft the nodes of `nodes` at `grafting_height` with `chunks`, the chunks from index
    /// `start_chunk`, when their chunk index is below `graftable`.
    pub(crate) const fn new(
        nodes: N,
        terms: &'a T,
        grafting_height: u32,
        start_chunk: u64,
        chunks: &'a [C],
        graftable: u64,
    ) -> Self {
        Self {
            nodes,
            terms,
            grafting_height,
            start_chunk,
            chunks,
            graftable,
        }
    }
}

impl<N, T, C> Nodes for Grafted<'_, N, T, C>
where
    N: Nodes<Digest = T::Digest>,
    T: Terms,
    C: AsRef<[u8]>,
{
    type Digest = T::Digest;

    fn children(&self, position: u64, height: u32) -> (u64, u64) {
        self.nodes.children(position, height)
    }

    fn leaf_digest(&self, position: u64, element: &[u8]) -> T::Digest {
        self.nodes.leaf_digest(position, element)
    }

    fn node_digest(
        &self,
        position: u64,
        height: u32,
        start: u64,
        left: &T::Digest,
        right: &T::Digest,
    ) -> T::Digest {
        let node = self.nodes.node_digest(position, height, start, left, right);
        if height != self.grafting_height {
            return node;
        }
        graft(
            self.terms,
            self.grafting_height,
            self.start_chunk,
            self.chunks,
            self.graftable,
            start,
            node,
        )
    }
}
