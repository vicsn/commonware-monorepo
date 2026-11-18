//! The production QMDB traversal and a single-item client for the DyLean experiment.
//!
//! [`adapter`] runs the pinned production traversal with callbacks that follow the production
//! hasher, and [`client`] decides whether a client accepts a claimed item. Both are generic over
//! [`terms::Terms`]: tests instantiate it with byte strings and SHA-256, and Lean instantiates the
//! hax extraction with DyLean's symbolic literal, concatenation and hash constructors.

#![forbid(unsafe_code)]

pub mod adapter;
pub mod client;
pub mod terms;

/// Production traversal, archived from the pinned revision by `check-bridge.sh`.
#[path = "../../.lake/rust/storage/src/merkle/proof/traversal.rs"]
#[allow(dead_code)]
mod traversal;

#[cfg(test)]
mod tests;
