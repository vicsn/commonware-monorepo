//! Types used to extract the production ordered proof's operation selection in isolation.
//! The proof payload stays opaque. The family parameter supplies its copyable location.
//! The interval comparisons instantiate the bounded half-open case of `contains_cyclic`.

use crate::cyclic;
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
