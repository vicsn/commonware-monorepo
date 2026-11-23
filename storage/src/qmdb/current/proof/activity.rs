//! Addressing an operation's activity bit within its bitmap chunk.

/// Offset of a location within its chunk. The caller validates the chunk bit width.
#[inline]
pub(crate) const fn offset(location: u64, bits: u64) -> u64 {
    location % bits
}

/// Whether the byte holds a set bit at this offset.
#[inline]
pub(crate) const fn is_set(byte: u8, offset: u64) -> bool {
    byte & (1 << (offset % 8)) != 0
}

/// Check the bit in its chunk after validating that `bits` equals the chunk width in bits.
#[inline]
pub(crate) const fn get(chunk: &[u8], location: u64, bits: u64) -> bool {
    let bit = offset(location, bits);
    is_set(chunk[(bit / 8) as usize], bit)
}
