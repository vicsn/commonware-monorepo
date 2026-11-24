use crate::{
    merkle::Family,
    qmdb::{
        any::operation::{
            Buffer, COMMIT_CONTEXT, DELETE_CONTEXT, Operation, OperationCodec, UPDATE_CONTEXT,
            Update, layout, update,
        },
        operation::read_commit_fixed,
        value::{FixedEncoding, FixedValue},
    },
};
use commonware_codec::{
    Buf, CodecFixed, Error as CodecError, FixedSize, ReadExt as _,
    util::{at_least, ensure_zeros},
};
use commonware_runtime::BufMut;
use commonware_utils::Array;

const fn widths<K: Array, V: FixedSize, S: FixedSize>() -> layout::Widths {
    layout::Widths {
        key: K::SIZE,
        value: V::SIZE,
        update: S::SIZE,
    }
}

const fn total_op_size<K: Array, V: FixedSize, S: FixedSize>() -> usize {
    widths::<K, V, S>().total()
}

impl<F, V, S> OperationCodec<F, S> for FixedEncoding<V>
where
    F: Family,
    S::Key: Array,
    V: FixedValue,
    S: Update<Value = V, ValueEncoding = Self> + CodecFixed<Cfg = ()>,
{
    type ReadCfg = ();

    fn write_operation(op: &Operation<F, S>, buf: &mut impl BufMut) {
        let operation = match op {
            Operation::Delete(k) => layout::Operation::Delete(k),
            Operation::Update(p) => layout::Operation::Update(p),
            Operation::Commit(metadata, floor_loc) => {
                layout::Operation::Commit(metadata.as_ref(), floor_loc.as_u64())
            }
        };
        layout::write_fixed(
            &mut Buffer::<_, S::Key, V, S>::new(buf),
            &widths::<S::Key, V, S>(),
            operation,
        );
    }

    fn read_operation(
        buf: &mut impl Buf,
        cfg: &Self::ReadCfg,
    ) -> Result<Operation<F, S>, CodecError> {
        let widths = widths::<S::Key, V, S>();
        let total = widths.total();
        at_least(buf, total)?;

        match u8::read(buf)? {
            DELETE_CONTEXT => {
                let key = S::Key::read(buf)?;
                ensure_zeros(buf, total - widths.delete())?;
                Ok(Operation::Delete(key))
            }
            UPDATE_CONTEXT => {
                let payload = S::read_cfg(buf, cfg)?;
                ensure_zeros(buf, total - widths.update_operation())?;
                Ok(Operation::Update(payload))
            }
            COMMIT_CONTEXT => {
                let (metadata, floor_loc) = read_commit_fixed(buf)?;
                ensure_zeros(buf, total - widths.commit())?;
                Ok(Operation::Commit(metadata, floor_loc))
            }
            e => Err(CodecError::InvalidEnum(e)),
        }
    }
}

// FixedSize for ordered fixed operations.
impl<F, K, V> FixedSize for Operation<F, update::Ordered<K, FixedEncoding<V>>>
where
    F: Family,
    K: Array,
    V: FixedValue,
    update::Ordered<K, FixedEncoding<V>>: FixedSize,
{
    const SIZE: usize = total_op_size::<K, V, update::Ordered<K, FixedEncoding<V>>>();
}

// FixedSize for unordered fixed operations.
impl<F, K, V> FixedSize for Operation<F, update::Unordered<K, FixedEncoding<V>>>
where
    F: Family,
    K: Array,
    V: FixedValue,
    update::Unordered<K, FixedEncoding<V>>: FixedSize,
{
    const SIZE: usize = total_op_size::<K, V, update::Unordered<K, FixedEncoding<V>>>();
}
