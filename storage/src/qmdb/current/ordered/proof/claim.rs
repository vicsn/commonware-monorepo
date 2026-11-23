//! Select the journal operation an ordered proof must authenticate.

use super::{
    Digest, ExclusionProof, Graftable, Key, Operation, OperationProof, Update, ValueEncoding,
    contains_cyclic,
};

/// Reconstruct a membership claim from the requested pair and the proof's successor.
pub(super) fn membership<F: Graftable, K: Key, V: ValueEncoding>(
    key: K,
    value: V::Value,
    next: &K,
) -> Operation<F, K, V> {
    Operation::Update(Update {
        key,
        value,
        next_key: next.clone(),
    })
}

/// An opening paired with the operation it must authenticate.
type Selected<'a, F, K, V, D, C> = (&'a OperationProof<F, D, C>, Operation<F, K, V>);

/// Select the operation and its opening, rejecting a key outside an exclusion interval.
pub(super) fn exclusion<'a, F: Graftable, K: Key, V: ValueEncoding, D: Digest, C>(
    key: &K,
    proof: &'a ExclusionProof<F, K, V, D, C>,
) -> Option<Selected<'a, F, K, V, D, C>> {
    match proof {
        ExclusionProof::KeyValue(op_proof, data) => {
            if data.key == *key || !contains_cyclic(&data.key..&data.next_key, key) {
                return None;
            }
            Some((op_proof, Operation::Update(data.clone())))
        }
        ExclusionProof::Commit(op_proof, metadata) => {
            Some((op_proof, Operation::Commit(metadata.clone(), op_proof.loc)))
        }
    }
}
