//! Abstract terms and snapshot access.
//!
//! The specification never inspects bytes. It only builds terms from literals, items and digests,
//! concatenates them and hashes them, so one definition serves both the concrete SHA-256 tests and
//! the symbolic DyLean proofs.

/// Constructors for the byte strings that the specification hashes.
pub trait Terms {
    /// Byte strings built from literals, items and digests.
    type Bytes;
    /// Hash outputs.
    type Digest: Copy + PartialEq;
    /// Stored items.
    type Item;

    /// A fixed byte string.
    fn literal(bytes: &[u8]) -> Self::Bytes;
    /// The bytes of an item.
    fn item(item: &Self::Item) -> Self::Bytes;
    /// The bytes of a digest.
    fn digest(digest: Self::Digest) -> Self::Bytes;
    /// The item carried by a received message, if any.
    fn parse(message: &Self::Bytes) -> Option<Self::Item>;
    /// The concatenation of two byte strings.
    fn concat(left: Self::Bytes, right: Self::Bytes) -> Self::Bytes;
    /// The digest of a byte string.
    fn hash(input: Self::Bytes) -> Self::Digest;
}

/// Read access to the items of an authenticated snapshot.
pub trait Store<I> {
    /// The item at `location`.
    fn item(&self, location: u64) -> I;
}
