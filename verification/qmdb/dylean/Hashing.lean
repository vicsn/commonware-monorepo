module
public import QmdbDylean.Extraction

/-! Trusted reading of the extracted `Terms` trait for an arbitrary hash function. A `Scheme` is a
hash function together with the encoding of the parts of a hash input into one message, and
`Scheme.terms` is the `Terms` implementation that hashes the encoded parts. `ByteHash.scheme` is
the production reading: the bytes of the parts are concatenated and hashed. -/

namespace Qmdb
open Aeneas Aeneas.Std CoreModels qmdb_dylean
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

/-- The encoding keeps hash inputs of one kind apart: a leaf input determines its element, a node
input its children and a root input its peak, each for fixed leading byte parts. -/
structure Scheme.Unambiguous (S : Scheme D M) : Prop where
  leaf : ∀ p a b : Slice Std.U8,
    S.encode [.Bytes p, .Bytes a] = S.encode [.Bytes p, .Bytes b] → a = b
  node : ∀ (p : Slice Std.U8) (l r l' r' : D),
    S.encode [.Bytes p, .Digest l, .Digest r] = S.encode [.Bytes p, .Digest l', .Digest r'] →
      l = l' ∧ r = r'
  root : ∀ (d n : Slice Std.U8) (x y : D),
    S.encode [.Bytes d, .Bytes n, .Digest x] = S.encode [.Bytes d, .Bytes n, .Digest y] → x = y

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
end Qmdb
