//! Shared range reconstruction in left-first DFS order.

/// Missing data while reconstructing an authenticated subtree.
pub(crate) enum Error {
    MissingElements,
    MissingDigests,
}

/// Streaming inputs, positioned hashing, and optional node collection.
pub(crate) trait Backend {
    type Digest: Copy;

    fn children(&self, position: u64, width: u64) -> (u64, u64);
    fn sibling(&mut self) -> Result<Self::Digest, Error>;
    fn leaf(&mut self, position: u64) -> Result<Self::Digest, Error>;
    fn node(
        &self,
        position: u64,
        width: u64,
        start: u64,
        left: Self::Digest,
        right: Self::Digest,
    ) -> Self::Digest;
    fn collect(
        &mut self,
        left_position: u64,
        left: Self::Digest,
        right_position: u64,
        right: Self::Digest,
    );
}

/// Reconstruct a valid perfect subtree, consuming inputs in left-first DFS order.
///
/// The caller supplies a positive power-of-two width with `start + width` fitting
/// in u64. The selected interval is half-open. Collection follows child hashing.
// Explicit matches keep fallible branches visible to extraction.
#[allow(clippy::question_mark)]
pub(crate) fn reconstruct<B: Backend>(
    backend: &mut B,
    position: u64,
    width: u64,
    start: u64,
    range_start: u64,
    range_end: u64,
) -> Result<B::Digest, Error> {
    if start + width <= range_start || start >= range_end {
        return backend.sibling();
    }
    if width == 1 {
        return backend.leaf(position);
    }
    let (left_position, right_position) = backend.children(position, width);
    let half = width / 2;
    let mid = start + half;
    let left = match reconstruct(backend, left_position, half, start, range_start, range_end) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let right = match reconstruct(backend, right_position, half, mid, range_start, range_end) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    backend.collect(left_position, left, right_position, right);
    Ok(backend.node(position, width, start, left, right))
}

/// Geometry and digests of the nodes of one Merkle family.
pub(crate) trait Nodes {
    /// Digest of a node.
    type Digest: Copy;

    /// Positions of the two children of the node at `position`, whose subtree has `2^height`
    /// leaves.
    fn children(&self, position: u64, height: u32) -> (u64, u64);

    /// Digest of the leaf at `position` holding `element`.
    fn leaf_digest(&self, position: u64, element: &[u8]) -> Self::Digest;

    /// Digest of the node at `position` whose children have digests `left` and `right`. The node
    /// has `2^height` leaves, the first at location `start`.
    fn node_digest(
        &self,
        position: u64,
        height: u32,
        start: u64,
        left: &Self::Digest,
        right: &Self::Digest,
    ) -> Self::Digest;
}

/// Receives the digests authenticated during reconstruction.
pub(crate) trait Collect<D> {
    /// Record the digests of the two children of a reconstructed node.
    fn collect(&mut self, left_position: u64, left: D, right_position: u64, right: D);

    /// Record the digest of a peak.
    fn peak(&mut self, position: u64, digest: D);
}

impl<D> Collect<D> for () {
    fn collect(&mut self, _: u64, _: D, _: u64, _: D) {}

    fn peak(&mut self, _: u64, _: D) {}
}

/// Reconstruction inputs: consecutive elements, sibling digests read from a cursor, and a
/// collector for computed child digests.
pub(crate) struct Opening<'a, N: Nodes, E, C> {
    nodes: N,
    elements: E,
    siblings: &'a [N::Digest],
    cursor: usize,
    collected: C,
}

impl<'a, N: Nodes, E, C> Opening<'a, N, E, C> {
    /// Read `elements` in order and `siblings` from index `cursor`.
    pub(crate) const fn new(
        nodes: N,
        elements: E,
        siblings: &'a [N::Digest],
        cursor: usize,
        collected: C,
    ) -> Self {
        Self {
            nodes,
            elements,
            siblings,
            cursor,
            collected,
        }
    }

    /// Index of the first unread sibling.
    pub(crate) const fn cursor(&self) -> usize {
        self.cursor
    }

    /// Record the digest of a peak with the collector.
    pub(crate) fn peak(&mut self, position: u64, digest: N::Digest)
    where
        C: Collect<N::Digest>,
    {
        self.collected.peak(position, digest);
    }

    /// Whether every element has been read.
    pub(crate) fn exhausted(&mut self) -> bool
    where
        E: Iterator,
    {
        self.elements.next().is_none()
    }
}

impl<N, E, C> Backend for Opening<'_, N, E, C>
where
    N: Nodes,
    E: Iterator<Item: AsRef<[u8]>>,
    C: Collect<N::Digest>,
{
    type Digest = N::Digest;

    fn children(&self, position: u64, width: u64) -> (u64, u64) {
        self.nodes.children(position, width.ilog2())
    }

    fn sibling(&mut self) -> Result<N::Digest, Error> {
        match self.siblings.get(self.cursor) {
            Some(&digest) => {
                self.cursor += 1;
                Ok(digest)
            }
            None => Err(Error::MissingDigests),
        }
    }

    fn leaf(&mut self, position: u64) -> Result<N::Digest, Error> {
        match self.elements.next() {
            Some(element) => Ok(self.nodes.leaf_digest(position, element.as_ref())),
            None => Err(Error::MissingElements),
        }
    }

    fn node(
        &self,
        position: u64,
        width: u64,
        start: u64,
        left: N::Digest,
        right: N::Digest,
    ) -> N::Digest {
        self.nodes
            .node_digest(position, width.ilog2(), start, &left, &right)
    }

    fn collect(
        &mut self,
        left_position: u64,
        left: N::Digest,
        right_position: u64,
        right: N::Digest,
    ) {
        self.collected
            .collect(left_position, left, right_position, right);
    }
}
