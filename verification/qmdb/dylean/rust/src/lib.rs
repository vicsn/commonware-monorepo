//! Rust specification of single-item QMDB inclusion for the DyLean experiment.
//!
//! [`spec`] defines the digests, the honest root and the verifier semantics. [`client`] decides
//! whether a client accepts a claimed item. [`adapter`] runs the pinned production traversal over
//! the same terms. Everything is generic over [`terms::Terms`]: tests instantiate it with byte
//! strings and SHA-256, and Lean instantiates the hax extraction with DyLean's symbolic literal,
//! concatenation and hash constructors.

#![forbid(unsafe_code)]

pub mod adapter;
pub mod client;
pub mod spec;
pub mod terms;

/// Production traversal, archived from the pinned revision by `check-bridge.sh`.
#[path = "../../.lake/rust/storage/src/merkle/proof/traversal.rs"]
#[allow(dead_code)]
mod traversal;

#[cfg(test)]
mod tests;
