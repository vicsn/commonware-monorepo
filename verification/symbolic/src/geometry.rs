//! The two Merkle families as the production reconstruction reads them.
//!
//! Production adapts any `merkle::Family` to [`Geometry`] by copying the peaks its family
//! iterates; each family iterates the peaks of its production geometry module. These instances
//! read the same geometry modules directly.

use crate::{
    mmb_geometry, mmr_geometry,
    reconstruct::{Geometry, Peaks},
};

/// The MMB family.
pub(crate) struct Mmb;

impl Peaks for mmb_geometry::Peaks {
    fn next(&mut self) -> Option<(u64, u32)> {
        mmb_geometry::Peaks::next(self)
    }
}

impl Geometry for Mmb {
    type Peaks = mmb_geometry::Peaks;

    fn domain(&self) -> u8 {
        mmb_geometry::DOMAIN
    }

    fn max_leaves(&self) -> u64 {
        mmb_geometry::MAX_LEAVES
    }

    fn peaks(&self, leaves: u64) -> mmb_geometry::Peaks {
        mmb_geometry::Peaks::new(leaves)
    }

    fn children(&self, position: u64, height: u32) -> (u64, u64) {
        mmb_geometry::children(position, height)
    }

    fn birth_offset(&self, height: u32) -> u64 {
        mmb_geometry::birth_offset(height)
    }
}

/// The MMR family.
pub(crate) struct Mmr;

impl Peaks for mmr_geometry::Peaks {
    fn next(&mut self) -> Option<(u64, u32)> {
        mmr_geometry::Peaks::next(self)
    }
}

impl Geometry for Mmr {
    type Peaks = mmr_geometry::Peaks;

    fn domain(&self) -> u8 {
        mmr_geometry::DOMAIN
    }

    fn max_leaves(&self) -> u64 {
        mmr_geometry::MAX_LEAVES
    }

    fn peaks(&self, leaves: u64) -> mmr_geometry::Peaks {
        mmr_geometry::Peaks::new(leaves)
    }

    fn children(&self, position: u64, height: u32) -> (u64, u64) {
        mmr_geometry::children(position, height)
    }

    fn birth_offset(&self, height: u32) -> u64 {
        mmr_geometry::birth_offset(height)
    }
}
