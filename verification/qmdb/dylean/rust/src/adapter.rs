//! Single-item verification through the pinned production traversal.

use crate::{
    spec,
    terms::Terms,
    traversal::{self, Backend, Error},
};

/// Traversal callbacks for one item and a cursor over its opening.
pub struct Opening<'a, T: Terms> {
    item: &'a T::Item,
    siblings: &'a [T::Digest],
    next: usize,
}

impl<T: Terms> Backend for Opening<'_, T> {
    type Digest = T::Digest;

    fn children(&self, position: u64, width: u64) -> (u64, u64) {
        (position - width, position - 1)
    }

    fn sibling(&mut self) -> Result<T::Digest, Error> {
        if self.next < self.siblings.len() {
            let digest = self.siblings[self.next];
            self.next += 1;
            Ok(digest)
        } else {
            Err(Error::MissingDigests)
        }
    }

    fn leaf(&mut self, position: u64) -> Result<T::Digest, Error> {
        Ok(spec::leaf::<T>(position, self.item))
    }

    fn node(&self, position: u64, left: T::Digest, right: T::Digest) -> T::Digest {
        spec::node::<T>(position, left, right)
    }

    fn collect(&mut self, _: u64, _: T::Digest, _: u64, _: T::Digest) {}
}

/// [`spec::verify_single`], with the peak rebuilt by the production traversal.
pub fn verify<T: Terms>(
    height: u32,
    location: u64,
    root: &T::Digest,
    item: &T::Item,
    siblings: &[T::Digest],
) -> bool {
    if height > spec::MAX_HEIGHT {
        return false;
    }
    let leaves = 1u64 << height;
    if location >= leaves {
        return false;
    }
    let mut opening = Opening::<T> {
        item,
        siblings,
        next: 0,
    };
    match traversal::reconstruct(
        &mut opening,
        2 * (leaves - 1),
        leaves,
        0,
        location,
        location + 1,
    ) {
        Ok(peak) => opening.next == siblings.len() && spec::wrap::<T>(height, peak) == *root,
        Err(_) => false,
    }
}
