//! The ordered client of Tempo's QMDB configuration, over stand-ins for the types that the
//! production operation selection names.
//!
//! The client selects the operation a proof must authenticate with production's `claim` module,
//! encodes it with production's fixed operation layout and verifies it with production's current
//! operation verifier over the MMB geometry, with the bagging of QMDB's operation roots. The
//! interval comparisons instantiate the bounded half-open case of `contains_cyclic`.

use crate::{
    BACKWARD_FOLD,
    current::{self, Fields},
    cyclic,
    geometry::Mmb,
    layout::{self, Widths, Writer},
    terms::Terms,
};
use core::ops::Range;

pub(crate) trait Graftable: Copy {}
pub(crate) trait Digest {}
pub(crate) trait Key: Clone + PartialEq {
    fn less(&self, other: &Self) -> bool;
}
pub(crate) trait ValueEncoding {
    type Value: Clone;
}

fn contains_cyclic<K: Key>(span: Range<&K>, key: &K) -> bool {
    cyclic::contains(
        !span.start.less(span.end),
        !key.less(span.start),
        key.less(span.end),
    )
}

pub(crate) struct Update<K: Key, V: ValueEncoding> {
    pub(crate) key: K,
    pub(crate) value: V::Value,
    pub(crate) next_key: K,
}

impl<K: Key, V: ValueEncoding> Clone for Update<K, V> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            value: self.value.clone(),
            next_key: self.next_key.clone(),
        }
    }
}

pub(crate) enum Operation<F: Graftable, K: Key, V: ValueEncoding> {
    Update(Update<K, V>),
    Commit(Option<V::Value>, F),
}

pub(crate) struct OperationProof<F: Graftable, D: Digest, C> {
    pub(crate) loc: F,
    pub(crate) payload: (D, C),
}

pub(crate) enum ExclusionProof<F: Graftable, K: Key, V: ValueEncoding, D: Digest, C> {
    KeyValue(OperationProof<F, D, C>, Update<K, V>),
    Commit(OperationProof<F, D, C>, Option<V::Value>),
}

/// The same operation reconstruction called by both production verify methods.
#[path = "../../../storage/src/qmdb/current/ordered/proof/claim.rs"]
pub(crate) mod claim;

/// An operation proof's material besides its location and ops root.
pub(crate) struct Payload<'a, D> {
    /// Leaves of the ops tree.
    pub(crate) leaves: u64,
    /// Inactive peaks of the ops tree.
    pub(crate) inactive: usize,
    /// The ops-tree range proof's digests.
    pub(crate) digests: &'a [D],
    /// Digest of the complete chunk whose ancestor is not yet born, if any.
    pub(crate) pending: Option<D>,
    /// Digest of the trailing partial chunk, if any.
    pub(crate) partial: Option<D>,
    /// The bitmap chunk holding the operation's activity bit.
    pub(crate) chunk: &'a [u8],
}

/// An operation proof whose payload is its ops root and its [`Payload`].
pub(crate) type Proof<'a, D> = OperationProof<u64, D, Payload<'a, D>>;

impl Graftable for u64 {}

/// Write `operation` in the fixed encoding with `writer`.
fn encode<K, V, W>(writer: &mut W, widths: &Widths, operation: &Operation<u64, K, V>)
where
    K: Key,
    V: ValueEncoding,
    W: Writer<Key = K, Value = V::Value, Update = Update<K, V>>,
{
    match operation {
        Operation::Update(update) => {
            layout::write_fixed(writer, widths, layout::Operation::Update(update));
        }
        Operation::Commit(metadata, floor) => {
            let metadata = match metadata {
                Some(value) => Some(value),
                None => None,
            };
            layout::write_fixed(writer, widths, layout::Operation::Commit(metadata, *floor));
        }
    }
}

/// Whether `proof` authenticates `operation` as active under `root`, encoding it with `writer`.
fn verify_selected<K, V, T, W>(
    terms: &T,
    widths: &Widths,
    writer: W,
    proof: &Proof<'_, T::Digest>,
    operation: &Operation<u64, K, V>,
    root: &T::Digest,
) -> bool
where
    K: Key,
    V: ValueEncoding,
    T: Terms,
    T::Digest: Digest,
    W: Writer<Key = K, Value = V::Value, Update = Update<K, V>> + AsRef<[u8]>,
{
    let mut writer = writer;
    encode(&mut writer, widths, operation);
    let fields = Fields {
        leaves: proof.payload.1.leaves,
        inactive: proof.payload.1.inactive,
        digests: proof.payload.1.digests,
        ops_root: proof.payload.0,
        pending: proof.payload.1.pending,
        partial: proof.payload.1.partial,
    };
    current::verify_operation(
        &Mmb,
        terms,
        BACKWARD_FOLD,
        true,
        &fields,
        proof.loc,
        proof.payload.1.chunk,
        writer.as_ref(),
        root,
    )
}

/// Whether `proof` authenticates that `key` has `value`, with `next` as the next active key, under
/// `root`, as production's `KeyValueProof::verify` decides.
#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_member<K, V, T, W>(
    terms: &T,
    widths: &Widths,
    writer: W,
    key: K,
    value: V::Value,
    next: &K,
    proof: &Proof<'_, T::Digest>,
    root: &T::Digest,
) -> bool
where
    K: Key,
    V: ValueEncoding,
    T: Terms,
    T::Digest: Digest,
    W: Writer<Key = K, Value = V::Value, Update = Update<K, V>> + AsRef<[u8]>,
{
    let operation = claim::membership::<u64, K, V>(key, value, next);
    verify_selected(terms, widths, writer, proof, &operation, root)
}

/// Whether `proof` authenticates that `key` has no value under `root`, as production's
/// `ExclusionProof::verify` decides.
pub(crate) fn verify_exclusion<'a, K, V, T, W>(
    terms: &T,
    widths: &Widths,
    writer: W,
    key: &K,
    proof: &ExclusionProof<u64, K, V, T::Digest, Payload<'a, T::Digest>>,
    root: &T::Digest,
) -> bool
where
    K: Key,
    V: ValueEncoding,
    T: Terms,
    T::Digest: Digest,
    W: Writer<Key = K, Value = V::Value, Update = Update<K, V>> + AsRef<[u8]>,
{
    match claim::exclusion(key, proof) {
        Some((selected, operation)) => {
            verify_selected(terms, widths, writer, selected, &operation, root)
        }
        None => false,
    }
}

#[cfg(test)]
mod tests;
