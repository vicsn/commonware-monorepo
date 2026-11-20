//! Rules of BLS12-381 certificates, over abstract keys and points.
//!
//! A certificate names its signers by index into an ordered committee and carries one signature.
//! The functions here fix what a verifier checks: which indices count, how many are required,
//! which keys are combined and which message the signature must cover. Production instantiates
//! [`Terms`] with BLS12-381 group operations. A symbolic model can instead read keys, hashing and
//! the signature check as abstract operations, so proofs about these functions apply unchanged.

/// Keys, hashed messages and signatures of one signature variant.
pub(crate) trait Terms {
    /// A public key, or a sum of public keys.
    type Public;

    /// A hashed message or a signature.
    type Point;

    /// The sum of no public keys.
    fn zero(&self) -> Self::Public;

    /// `sum` extended by `key`.
    fn add(&self, sum: Self::Public, key: &Self::Public) -> Self::Public;

    /// The point that a signature over `message` in `namespace` is checked against.
    fn message(&self, namespace: &[u8], message: &[u8]) -> Self::Point;

    /// Whether `signature` signs `hashed` under `key`.
    fn check(&self, key: &Self::Public, hashed: &Self::Point, signature: &Self::Point) -> bool;
}

/// An ordered committee whose member `index` holds the key `key(index)`.
pub(crate) trait Committee<K> {
    /// Number of members.
    fn members(&self) -> u64;

    /// Number of members that a certificate must name. Only asked of a committee whose size a
    /// certificate has matched.
    fn quorum(&self) -> u64;

    /// The key of member `index`, if there is such a member.
    fn key(&self, index: u64) -> Option<&K>;
}

/// The signer indices that a certificate claims, one flag per index below `bound`.
pub(crate) trait Signers {
    /// Number of indices that the certificate can name.
    fn bound(&self) -> u64;

    /// Whether the certificate names `index`, which is below `bound`.
    fn names(&self, index: u64) -> bool;
}

/// A value that is decoded when it is first needed.
pub(crate) trait Decoded<T> {
    /// The value, if it decodes.
    fn decoded(&self) -> Option<&T>;
}

/// Number of indices that `signers` names.
pub(crate) fn count<B: Signers>(signers: &B) -> u64 {
    let bound = signers.bound();
    let mut count = 0;
    let mut index = 0;
    while index < bound {
        if signers.names(index) {
            count += 1;
        }
        index += 1;
    }
    count
}

/// Sum of the keys of the members that `signers` names, in index order, or `None` if it names an
/// index that has no member.
pub(crate) fn aggregate<T, C, B>(terms: &T, committee: &C, signers: &B) -> Option<T::Public>
where
    T: Terms,
    C: Committee<T::Public>,
    B: Signers,
{
    let bound = signers.bound();
    let mut sum = terms.zero();
    let mut index = 0;
    while index < bound {
        if signers.names(index) {
            match committee.key(index) {
                Some(key) => sum = terms.add(sum, key),
                None => return None,
            }
        }
        index += 1;
    }
    Some(sum)
}

/// Whether `signature` certifies `message` in `namespace` for `committee`.
///
/// The certificate must name indices of exactly this committee and at least its quorum of them,
/// and its signature must sign the message under the sum of the keys of the members it names.
/// Keys are only combined once these counts hold and the signature decodes.
pub(crate) fn verify_certificate<T, C, B, S>(
    terms: &T,
    committee: &C,
    signers: &B,
    signature: &S,
    namespace: &[u8],
    message: &[u8],
) -> bool
where
    T: Terms,
    C: Committee<T::Public>,
    B: Signers,
    S: Decoded<T::Point>,
{
    if signers.bound() != committee.members() {
        return false;
    }
    if count(signers) < committee.quorum() {
        return false;
    }
    let signature = match signature.decoded() {
        Some(signature) => signature,
        None => return false,
    };
    let key = match aggregate(terms, committee, signers) {
        Some(key) => key,
        None => return false,
    };
    terms.check(&key, &terms.message(namespace, message), signature)
}

/// Whether `signature` is the signature of member `signer` over `message` in `namespace`.
pub(crate) fn verify_attestation<T, C, S>(
    terms: &T,
    committee: &C,
    signer: u64,
    signature: &S,
    namespace: &[u8],
    message: &[u8],
) -> bool
where
    T: Terms,
    C: Committee<T::Public>,
    S: Decoded<T::Point>,
{
    let key = match committee.key(signer) {
        Some(key) => key,
        None => return false,
    };
    let signature = match signature.decoded() {
        Some(signature) => signature,
        None => return false,
    };
    terms.check(key, &terms.message(namespace, message), signature)
}

/// Whether `signature` signs `message` in `namespace` under the single key `identity`.
pub(crate) fn verify_identity<T, S>(
    terms: &T,
    identity: &T::Public,
    signature: &S,
    namespace: &[u8],
    message: &[u8],
) -> bool
where
    T: Terms,
    S: Decoded<T::Point>,
{
    let signature = match signature.decoded() {
        Some(signature) => signature,
        None => return false,
    };
    terms.check(identity, &terms.message(namespace, message), signature)
}
