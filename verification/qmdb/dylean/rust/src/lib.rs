//! Production QMDB traversal and hash-input encodings, with a single-item client, for the DyLean
//! experiment.
//!
//! The production modules are included unchanged. [`client`] lays out an MMR with one peak, runs
//! the production traversal and hashes the peak into the root with the production encoding. Hax
//! extracts everything; Lean instantiates the encodings' [`Terms`](terms::Terms) with DyLean's
//! symbolic constructors, and the tests instantiate them with SHA-256.

#![forbid(unsafe_code)]
// The crate exists for extraction and tests, so nothing is public.
#![allow(dead_code)]

pub(crate) mod client;

/// Production hash-input encodings.
#[path = "../../../../../storage/src/merkle/hasher/terms.rs"]
pub(crate) mod terms;

/// Production traversal and its callbacks.
#[path = "../../../../../storage/src/merkle/proof/traversal.rs"]
pub(crate) mod traversal;

#[cfg(test)]
mod tests;
