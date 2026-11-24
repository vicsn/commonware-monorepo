//! Wire tags that open every encoded QMDB operation.
//!
//! One table serves every database, so no tag stands for two kinds of operation.

/// Wire tag for a commit operation. Every database tags its commits alike.
pub const COMMIT_CONTEXT: u8 = 0;
/// Wire tag for an update operation of an [any](crate::qmdb::any) or
/// [current](crate::qmdb::current) database.
pub const UPDATE_CONTEXT: u8 = 1;
/// Wire tag for a delete operation of an [any](crate::qmdb::any) or
/// [current](crate::qmdb::current) database.
pub const DELETE_CONTEXT: u8 = 2;
/// Wire tag for a set operation of an [immutable](crate::qmdb::immutable) database.
pub const SET_CONTEXT: u8 = 3;
/// Wire tag for an append operation of a [keyless](crate::qmdb::keyless) database.
pub const APPEND_CONTEXT: u8 = 4;
