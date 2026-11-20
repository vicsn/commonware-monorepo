//! What every client shares.
//!
//! A client step is pure: it takes the client's trusted state, a received message and
//! adversary-chosen parameters, and returns the event to log, or `None` to reject. It performs no
//! I/O, reads no clock and draws no randomness. Lean runs an extracted step inside DyLean: receive
//! a message, run the step, then log the event or fail.

/// Received messages that may carry an item.
pub(crate) trait Messages {
    /// A received message.
    type Message;

    /// The item that `message` carries, if any.
    fn parse<'a>(&self, message: &'a Self::Message) -> Option<&'a [u8]>;
}
