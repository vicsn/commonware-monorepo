module
public import Commonware.Symbolic.Terms
public import DY.EquationalTheory.Sign
public import DY.EquationalTheory.DiffieHellman
public import Commonware.Symbolic.Mac
public import DY.Actions.Random

/-! SAKE's term algebra and the reading of the extracted handshake rules in DyLean. Trusted.
`#combine` fixes DyLean's bytes to fresh values, literals, concatenation, hashing, signatures,
Diffie-Hellman and message authentication codes.

A transcript is read as the term of everything committed to it, in order, starting from a hash
of the namespace. Signing a transcript signs its hash. The secret that two ephemeral keys share
is DyLean's Diffie-Hellman term, and the exchange is always contributory. A confirmation is the
message authentication code of the confirmation's label under the hash of the transcript:
production computes it with BLAKE3 keyed by the transcript's summary. `Opening` and `Exchange`
name what a handshake agrees on in public. -/

namespace Sake
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,
  Mac,

/-- A timestamp as a term: the literal of its big-endian bytes. -/
def stamp (time : Std.U64) : Bytes :=
  Literal.literalToBytes
    (toByteArray (Aeneas.Std.core.num.U64.to_be_bytes time).to_slice)

/-- The transcript that both peers start from in a namespace. -/
def start (ns : ByteArray) : Bytes :=
  Hash.hash (Literal.literalToBytes ns)

/-- The extracted `Terms` on DyLean terms. -/
def sakeTerms : sake.Terms Unit Bytes Bytes Bytes Bytes where
  time _ transcript time := RustM.ok (Concat.concat transcript (stamp time))
  ephemeral _ transcript key := RustM.ok (Concat.concat transcript key)
  «public» _ secret := RustM.ok (DiffieHellman.dhPk secret)
  exchange _ transcript secret peer :=
    RustM.ok (true, Concat.concat transcript (DiffieHellman.dh peer secret))
  confirmation _ transcript label :=
    RustM.ok (Mac.mac (Hash.hash transcript)
      (Literal.literalToBytes (toByteArray label)))
  same _ a b := RustM.ok (decide (a = b))

/-- A local identity: its signing key and the nonce of its next signature.
DyLean's signatures take a nonce, and a step signs at most once. -/
structure Signer where
  /-- The signing key. -/
  key : Bytes
  /-- The nonce of the next signature. -/
  nonce : Bytes

/-- The extracted `Identity` on DyLean terms: an identity commits its
verification key and signs the hash of a transcript. -/
def signer : sake.Identity Signer Bytes Bytes where
  commit identity transcript :=
    RustM.ok (Concat.concat transcript (Signature.vk identity.key))
  sign identity transcript :=
    RustM.ok (Signature.sign identity.key identity.nonce (Hash.hash transcript))

/-- The extracted `Peer` on DyLean terms: a peer is its verification key. -/
def peer : sake.Peer Bytes Bytes Bytes where
  commit key transcript := RustM.ok (Concat.concat transcript key)
  verify key transcript signature :=
    RustM.ok (Signature.verify key (Hash.hash transcript) signature)

/-- The extracted `Fresh` on DyLean terms: a secret that the protocol drew
before the step runs. -/
def fresh : sake.Fresh Bytes Bytes where
  draw secret := RustM.ok secret

/-- What a dialer fixes when it starts a handshake. -/
structure Opening where
  /-- The application namespace. -/
  ns : ByteArray
  /-- The dialer's identity key. -/
  dialer : Bytes
  /-- The listener's identity key. -/
  listener : Bytes
  /-- The dialer's timestamp. -/
  dialed : Std.U64
  /-- The dialer's ephemeral public key. -/
  dialerKey : Bytes

/-- What both peers of a handshake agree on in public: the opening and what
the listener adds to it. -/
structure Exchange extends Opening where
  /-- The listener's timestamp. -/
  answered : Std.U64
  /-- The listener's ephemeral public key. -/
  listenerKey : Bytes

end
end Sake
