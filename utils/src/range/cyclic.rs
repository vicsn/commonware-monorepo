//! Membership after comparing the key to both endpoints.

/// Combine the endpoint comparisons, allowing a span to cross the end of the key domain.
pub(super) const fn contains(wraps: bool, after_start: bool, before_end: bool) -> bool {
    if wraps {
        after_start || before_end
    } else {
        after_start && before_end
    }
}
