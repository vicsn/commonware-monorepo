//! Rust that hax extracts for the symbolic (DyLean) proofs.
//!
//! Production modules are included unchanged through `#[path]`, so the proofs cover the code that
//! production runs. [`client`] fixes what every client shares. A verified target adds a module
//! where production does not already state the whole client: [`inclusion`] accepts one claimed item
//! of an MMR with one peak, [`reads`] checks ordered reads under a current root, and [`bls`]
//! supplies the quorum of a committee. The steps of the SAKE
//! handshake are production's own, in [`sake`]. Hax extracts the whole crate into one Lean
//! package, so all targets share one extraction of the production modules and of [`client`]. Lean
//! instantiates [`Terms`](terms::Terms) and [`Messages`](client::Messages) with DyLean's symbolic
//! constructors; the tests instantiate them with SHA-256.

#![forbid(unsafe_code)]
// The crate exists for extraction and tests, so nothing is public.
#![allow(dead_code)]

/// Production rules for addressing an operation's activity bit.
#[path = "../../../storage/src/qmdb/current/proof/activity.rs"]
pub(crate) mod activity;

/// Production verification of current range and operation proofs.
#[path = "../../../storage/src/qmdb/current/proof/rules.rs"]
pub(crate) mod current;

pub(crate) mod geometry;

/// Production grafting of bitmap chunks onto ops-tree nodes.
#[path = "../../../storage/src/qmdb/current/grafting/rules.rs"]
pub(crate) mod grafting;

/// Production field order, tags and padding of encoded operations.
#[path = "../../../storage/src/qmdb/any/operation/layout.rs"]
pub(crate) mod layout;

/// Production node positions and peaks of an MMB.
#[path = "../../../storage/src/merkle/mmb/geometry.rs"]
pub(crate) mod mmb_geometry;

/// Production node positions and peaks of an MMR.
#[path = "../../../storage/src/merkle/mmr/geometry.rs"]
pub(crate) mod mmr_geometry;

/// Production range-proof root reconstruction.
#[path = "../../../storage/src/merkle/proof/reconstruct.rs"]
pub(crate) mod reconstruct;

/// Production wire tags of operations.
#[path = "../../../storage/src/qmdb/operation/tags.rs"]
pub(crate) mod tags;

pub(crate) mod bls;
pub(crate) mod client;

/// Production cyclic range decision for QMDB successor intervals.
#[path = "../../../utils/src/range/cyclic.rs"]
pub(crate) mod cyclic;

pub(crate) mod inclusion;

/// Domain byte of backward-fold peak bagging, the bagging of QMDB's operation roots.
pub(crate) const BACKWARD_FOLD: u8 = 1;

/// The module paths that the included QMDB production files name.
pub(crate) mod qmdb {
    pub(crate) mod current {
        pub(crate) mod grafting {
            pub(crate) use crate::grafting as rules;
        }
    }
    pub(crate) mod operation {
        pub(crate) use crate::tags;
    }
}

pub(crate) mod reads;

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

/// The module paths that the included production files name.
pub(crate) mod merkle {
    pub(crate) mod hasher {
        pub(crate) use crate::terms;
    }
    pub(crate) mod proof {
        pub(crate) use crate::{reconstruct, traversal};
    }
}

#[cfg(test)]
mod concrete;
