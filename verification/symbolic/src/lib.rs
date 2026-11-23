//! Rust that hax extracts for the symbolic (DyLean) proofs.
//!
//! Production modules are included unchanged through `#[path]`, so the proofs cover the code that
//! production runs. [`client`] fixes what every client shares. A verified target adds a module
//! where production does not already state the whole client: [`qmdb`] accepts one claimed item of
//! an MMR with one peak, and [`bls`] supplies the quorum of a committee. The steps of the SAKE
//! handshake are production's own, in [`sake`]. Hax extracts the whole crate into one Lean
//! package, so all targets share one extraction of the production modules and of [`client`]. Lean
//! instantiates [`Terms`](terms::Terms) and [`Messages`](client::Messages) with DyLean's symbolic
//! constructors; the tests instantiate them with SHA-256.

#![forbid(unsafe_code)]
// The crate exists for extraction and tests, so nothing is public.
#![allow(dead_code)]

pub(crate) mod bls;
pub(crate) mod client;
pub(crate) mod qmdb;

/// Production rules of BLS12-381 certificates.
#[path = "../../../cryptography/src/bls12381/certificate/rules.rs"]
pub(crate) mod rules;

/// Production rules of the SAKE handshake.
#[path = "../../../cryptography/src/handshake/sake/rules.rs"]
pub(crate) mod sake;

/// Production hash-input encodings of Merkle-family digests.
#[path = "../../../storage/src/merkle/hasher/terms.rs"]
pub(crate) mod terms;

/// Production proof traversal and its callbacks.
#[path = "../../../storage/src/merkle/proof/traversal.rs"]
pub(crate) mod traversal;

#[cfg(test)]
mod concrete;
