module
public import CommonwareSymbolic.Extraction

/-! Trusted reading of the extracted production `Terms` trait for an arbitrary hash function. A
`Scheme` is a hash function together with the encoding of the parts of a hash input into one
message, and `Scheme.terms` is the `Terms` implementation that hashes the encoded parts.
`ByteHash.scheme` is the production reading: the bytes of the parts are concatenated and
hashed. -/

namespace Commonware.Symbolic
open Aeneas Aeneas.Std CoreModels commonware_symbolic
@[expose] public section

/-- A hash function from messages `M` to digests `D`, with the encoding of the parts of a hash
input into one message. -/
structure Scheme (D M : Type) where
  hash : M → D
  encode : List (terms.Part D) → M

variable {D M : Type}

/-- The `Terms` implementation of a scheme: hash the encoded parts and compare digests by
equality. -/
def Scheme.terms [DecidableEq D] (S : Scheme D M) : terms.Terms Unit D where
  coremarkerCopyInst := ⟨⟨RustM.ok, fun _ x => RustM.ok x⟩⟩
  corecmpPartialEqInst :=
    { eq := fun a b => RustM.ok (decide (a = b)), ne := fun a b => RustM.ok (!decide (a = b)) }
  hash _ parts := RustM.ok (S.hash (S.encode parts.val))

/-- Two different messages with the same digest. -/
def Scheme.Collision (S : Scheme D M) (x y : M) : Prop :=
  x ≠ y ∧ S.hash x = S.hash y

/-- A hash over byte strings whose digests have a fixed-length, injective byte representation. -/
structure ByteHash (D : Type) where
  hash : List Std.U8 → D
  bytes : D → List Std.U8
  size : Nat
  bytes_length : ∀ d, (bytes d).length = size
  bytes_inj : ∀ a b, bytes a = bytes b → a = b

/-- Production hashing, as `ByteTerms` in `storage/src/merkle/hasher.rs`: the bytes of the parts
are concatenated and hashed. -/
def ByteHash.scheme (B : ByteHash D) : Scheme D (List Std.U8) where
  hash := B.hash
  encode parts := parts.flatMap fun
    | .Bytes s => s.val
    | .Digest d => B.bytes d

end
end Commonware.Symbolic
