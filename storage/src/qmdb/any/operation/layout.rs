//! Field order, wire tags and zero padding of encoded operations over an abstract writer.
//!
//! The fixed operation codec and the update codecs write through these functions. They use no
//! codec types, so the symbolic verification extracts this file unchanged.

use crate::qmdb::operation::tags::{COMMIT_CONTEXT, DELETE_CONTEXT, UPDATE_CONTEXT};

/// Appends the parts of an encoded operation.
pub(crate) trait Writer {
    /// A key.
    type Key;
    /// A value.
    type Value;
    /// An update payload.
    type Update;

    /// Append one byte.
    fn byte(&mut self, byte: u8);

    /// Append `count` zero bytes.
    fn zeros(&mut self, count: usize);

    /// Append a big-endian `u64`.
    fn word(&mut self, word: u64);

    /// Append the encoding of a key.
    fn key(&mut self, key: &Self::Key);

    /// Append the encoding of a value.
    fn value(&mut self, value: &Self::Value);

    /// Append the encoding of an update payload.
    fn update(&mut self, update: &Self::Update);
}

/// An operation to encode, borrowing its fields.
pub(crate) enum Operation<'a, K, V, U> {
    /// Delete a key.
    Delete(&'a K),
    /// Apply an update payload.
    Update(&'a U),
    /// Commit with optional metadata and an inactivity floor.
    Commit(Option<&'a V>, u64),
}

/// Encoded widths, in bytes, of the fields of one database's fixed-size operations.
pub(crate) struct Widths {
    /// Width of a key.
    pub(crate) key: usize,
    /// Width of a value.
    pub(crate) value: usize,
    /// Width of an update payload.
    pub(crate) update: usize,
}

impl Widths {
    /// Unpadded width of a delete, tag included.
    pub(crate) const fn delete(&self) -> usize {
        1 + self.key
    }

    /// Unpadded width of an update, tag included.
    pub(crate) const fn update_operation(&self) -> usize {
        1 + self.update
    }

    /// Unpadded width of a commit, tag included: presence byte, value and floor.
    pub(crate) const fn commit(&self) -> usize {
        1 + 1 + self.value + 8
    }

    /// Width every operation is padded to: the largest unpadded width.
    pub(crate) const fn total(&self) -> usize {
        let mut total = self.update_operation();
        if self.commit() > total {
            total = self.commit();
        }
        if self.delete() > total {
            total = self.delete();
        }
        total
    }
}

/// Write `operation` in the fixed encoding: its tag, its fields, then zeros up to
/// [`Widths::total`]. A commit writes a presence byte and its value, or zeros of the same width,
/// then its floor.
pub(crate) fn write_fixed<W: Writer>(
    writer: &mut W,
    widths: &Widths,
    operation: Operation<'_, W::Key, W::Value, W::Update>,
) {
    let total = widths.total();
    match operation {
        Operation::Delete(key) => {
            writer.byte(DELETE_CONTEXT);
            writer.key(key);
            writer.zeros(total - widths.delete());
        }
        Operation::Update(update) => {
            writer.byte(UPDATE_CONTEXT);
            writer.update(update);
            writer.zeros(total - widths.update_operation());
        }
        Operation::Commit(metadata, floor) => {
            writer.byte(COMMIT_CONTEXT);
            match metadata {
                Some(value) => {
                    writer.byte(1);
                    writer.value(value);
                }
                None => writer.zeros(1 + widths.value),
            }
            writer.word(floor);
            writer.zeros(total - widths.commit());
        }
    }
}

/// Write an ordered update payload: its key, its value, then the next key.
pub(crate) fn write_ordered_update<W: Writer>(
    writer: &mut W,
    key: &W::Key,
    value: &W::Value,
    next_key: &W::Key,
) {
    writer.key(key);
    writer.value(value);
    writer.key(next_key);
}
