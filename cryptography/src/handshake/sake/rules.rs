//! Rules of the SAKE handshake, over abstract transcripts, signatures and key exchange.
//!
//! The functions here fix what each peer commits, signs and checks, and in which order.
//! Production instantiates [`Terms`], [`Identity`] and [`Peer`] with BLAKE3 transcripts, X25519
//! and the identity signatures of its peers. A symbolic model can instead read these as abstract
//! operations, so proofs about these functions apply unchanged.

/// Label of the confirmation that the listener sends.
const LABEL_CONFIRMATION_L2D: &[u8] = b"confirmation_l2d";

/// Label of the confirmation that the dialer sends.
const LABEL_CONFIRMATION_D2L: &[u8] = b"confirmation_d2l";

/// Transcripts and key exchange of one handshake.
pub(crate) trait Terms {
    /// A transcript of what both peers have committed.
    type Transcript;

    /// A value derived from a transcript that confirms its holder knows it.
    type Confirmation;

    /// An ephemeral public key.
    type Ephemeral;

    /// An ephemeral secret key.
    type Secret;

    /// Commit a timestamp.
    fn time(&self, transcript: &mut Self::Transcript, time_ms: u64);

    /// Commit an ephemeral public key.
    fn ephemeral(&self, transcript: &mut Self::Transcript, key: &Self::Ephemeral);

    /// The public key of `secret`.
    fn public(&self, secret: &Self::Secret) -> Self::Ephemeral;

    /// Commit the secret that `secret` shares with `peer`. Returns false, with nothing to rely
    /// on in `transcript`, if the exchange is not contributory.
    fn exchange(
        &self,
        transcript: &mut Self::Transcript,
        secret: Self::Secret,
        peer: &Self::Ephemeral,
    ) -> bool;

    /// The confirmation of `transcript` for `label`.
    fn confirmation(
        &self,
        transcript: &Self::Transcript,
        label: &'static [u8],
    ) -> Self::Confirmation;

    /// Whether two confirmations are equal.
    fn same(&self, a: &Self::Confirmation, b: &Self::Confirmation) -> bool;
}

/// The local identity, which commits itself to transcripts `X` and signs them.
pub(crate) trait Identity<X> {
    /// A signature of this identity.
    type Signature;

    /// Commit this identity.
    fn commit(&self, transcript: &mut X);

    /// Sign `transcript` as this identity.
    fn sign(&self, transcript: &X) -> Self::Signature;
}

/// The identity of the peer, which is committed to transcripts `X` and whose signatures of them
/// are checked.
pub(crate) trait Peer<X> {
    /// A signature of this identity.
    type Signature;

    /// Commit this identity.
    fn commit(&self, transcript: &mut X);

    /// Whether `signature` signs `transcript` as this identity.
    fn verify(&self, transcript: &X, signature: &Self::Signature) -> bool;
}

/// An ephemeral secret that is drawn when it is first needed.
pub(crate) trait Fresh<S> {
    /// The secret.
    fn draw(self) -> S;
}

/// The peer timestamps that a step accepts: `start..end`, in milliseconds.
pub(crate) struct Window {
    /// The first accepted timestamp.
    pub(crate) start: u64,
    /// The first timestamp after the accepted ones.
    pub(crate) end: u64,
}

impl Window {
    /// Whether `time_ms` is accepted.
    const fn contains(&self, time_ms: u64) -> bool {
        self.start <= time_ms && time_ms < self.end
    }
}

/// What a peer brings to its first step.
pub(crate) struct Context<'a, X, S, P> {
    /// Whether the dialer's identity is committed before the first signature.
    pub(crate) early: bool,
    /// The transcript that both peers start from.
    pub(crate) transcript: X,
    /// The local time in milliseconds.
    pub(crate) now: u64,
    /// The peer timestamps that are accepted.
    pub(crate) window: Window,
    /// The local identity.
    pub(crate) signer: &'a S,
    /// The identity expected of the peer.
    pub(crate) peer: &'a P,
}

/// The first message, from the dialer.
pub(crate) struct Syn<E, G> {
    /// The dialer's time in milliseconds.
    pub(crate) time_ms: u64,
    /// The dialer's ephemeral public key.
    pub(crate) epk: E,
    /// The dialer's signature of the transcript so far.
    pub(crate) sig: G,
}

/// The second message, from the listener.
pub(crate) struct SynAck<E, G, C> {
    /// The listener's time in milliseconds.
    pub(crate) time_ms: u64,
    /// The listener's ephemeral public key.
    pub(crate) epk: E,
    /// The listener's signature of the transcript so far.
    pub(crate) sig: G,
    /// The listener's confirmation of the secret transcript.
    pub(crate) confirmation: C,
}

/// Why a step rejects a message.
pub(crate) enum Rejection {
    /// The peer's timestamp is outside the accepted range.
    Timestamp,
    /// The peer's signature does not sign the transcript.
    Signature,
    /// The key exchange is not contributory.
    Ephemeral,
    /// The peer's confirmation is not that of the local transcript.
    Confirmation,
}

/// Start a handshake as the dialer. Returns the ephemeral secret and transcript to keep, and the
/// message to send.
#[allow(clippy::type_complexity)]
pub(crate) fn dial_start<T, I, P, F>(
    terms: &T,
    context: Context<'_, T::Transcript, I, P>,
    fresh: F,
) -> (T::Secret, T::Transcript, Syn<T::Ephemeral, I::Signature>)
where
    T: Terms,
    I: Identity<T::Transcript>,
    P: Peer<T::Transcript>,
    F: Fresh<T::Secret>,
{
    let Context {
        early,
        mut transcript,
        now,
        window: _,
        signer,
        peer,
    } = context;
    let secret = fresh.draw();
    let epk = terms.public(&secret);
    terms.time(&mut transcript, now);
    peer.commit(&mut transcript);
    if early {
        signer.commit(&mut transcript);
    }
    terms.ephemeral(&mut transcript, &epk);
    let sig = signer.sign(&transcript);
    if !early {
        signer.commit(&mut transcript);
    }
    (
        secret,
        transcript,
        Syn {
            time_ms: now,
            epk,
            sig,
        },
    )
}

/// Answer the first message as the listener. Returns the transcript to keep and the message to
/// send. The ephemeral secret is drawn only once the dialer's signature verifies.
#[allow(clippy::type_complexity)]
pub(crate) fn listen_start<T, I, P, F>(
    terms: &T,
    context: Context<'_, T::Transcript, I, P>,
    fresh: F,
    msg: &Syn<T::Ephemeral, P::Signature>,
) -> Result<
    (
        T::Transcript,
        SynAck<T::Ephemeral, I::Signature, T::Confirmation>,
    ),
    Rejection,
>
where
    T: Terms,
    I: Identity<T::Transcript>,
    P: Peer<T::Transcript>,
    F: Fresh<T::Secret>,
{
    let Context {
        early,
        mut transcript,
        now,
        window,
        signer,
        peer,
    } = context;
    if !window.contains(msg.time_ms) {
        return Err(Rejection::Timestamp);
    }
    terms.time(&mut transcript, msg.time_ms);
    signer.commit(&mut transcript);
    if early {
        peer.commit(&mut transcript);
    }
    terms.ephemeral(&mut transcript, &msg.epk);
    if !peer.verify(&transcript, &msg.sig) {
        return Err(Rejection::Signature);
    }
    if !early {
        peer.commit(&mut transcript);
    }
    let secret = fresh.draw();
    let epk = terms.public(&secret);
    terms.time(&mut transcript, now);
    terms.ephemeral(&mut transcript, &epk);
    let sig = signer.sign(&transcript);
    if !terms.exchange(&mut transcript, secret, &msg.epk) {
        return Err(Rejection::Ephemeral);
    }
    let confirmation = terms.confirmation(&transcript, LABEL_CONFIRMATION_L2D);
    Ok((
        transcript,
        SynAck {
            time_ms: now,
            epk,
            sig,
            confirmation,
        },
    ))
}

/// Finish a handshake as the dialer, from what [`dial_start`] kept. Returns the confirmation to
/// send and the secret transcript.
pub(crate) fn dial_end<T, P>(
    terms: &T,
    secret: T::Secret,
    mut transcript: T::Transcript,
    peer: &P,
    window: &Window,
    msg: &SynAck<T::Ephemeral, P::Signature, T::Confirmation>,
) -> Result<(T::Confirmation, T::Transcript), Rejection>
where
    T: Terms,
    P: Peer<T::Transcript>,
{
    if !window.contains(msg.time_ms) {
        return Err(Rejection::Timestamp);
    }
    terms.time(&mut transcript, msg.time_ms);
    terms.ephemeral(&mut transcript, &msg.epk);
    if !peer.verify(&transcript, &msg.sig) {
        return Err(Rejection::Signature);
    }
    if !terms.exchange(&mut transcript, secret, &msg.epk) {
        return Err(Rejection::Ephemeral);
    }
    let listener = terms.confirmation(&transcript, LABEL_CONFIRMATION_L2D);
    let dialer = terms.confirmation(&transcript, LABEL_CONFIRMATION_D2L);
    if !terms.same(&msg.confirmation, &listener) {
        return Err(Rejection::Confirmation);
    }
    Ok((dialer, transcript))
}

/// Finish a handshake as the listener, from the transcript that [`listen_start`] kept and the
/// dialer's confirmation. Returns the secret transcript, or `None` if the confirmation is not
/// that of the transcript.
pub(crate) fn listen_end<T: Terms>(
    terms: &T,
    transcript: T::Transcript,
    confirmation: &T::Confirmation,
) -> Option<T::Transcript> {
    let dialer = terms.confirmation(&transcript, LABEL_CONFIRMATION_D2L);
    if !terms.same(confirmation, &dialer) {
        return None;
    }
    Some(transcript)
}
