module
public import Hashing
public import DY.EquationalTheory.Hash
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.Literal

/-! Trusted glue between the extracted Rust and DyLean. `symbolic` reads the production hash
inputs symbolically: byte parts are literals, digest parts are terms, parts are concatenated to
the right and hashing is DyLean's hash constructor. `messages` reads a claimed item from a
literal message. `Snapshot` is the authenticated historical snapshot that the application
supplies. -/

namespace Qmdb
open DY Aeneas Aeneas.Std CoreModels qmdb_dylean
@[expose] public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Literal,
  Concat,
  Hash,

/-- The bytes of a Rust byte slice. -/
def toByteArray (s : Slice Std.U8) : ByteArray :=
  ⟨(s.val.map fun b => UInt8.ofNat b.val).toArray⟩

/-- A hash-input part as a term. -/
def part : terms.Part Bytes → Bytes
  | .Bytes s => Literal.literalToBytes (toByteArray s)
  | .Digest d => d

/-- Parts concatenated to the right. -/
def chain : List (terms.Part Bytes) → Bytes
  | [] => Literal.literalToBytes ByteArray.empty
  | [p] => part p
  | p :: rest => Concat.concat (part p) (chain rest)

/-- Symbolic hashing: DyLean's hash constructor over the concatenated parts. -/
def symbolic : Scheme Bytes Bytes where
  hash := Hash.hash
  encode := chain

/-- The production hash inputs as DyLean terms. -/
abbrev dyTerms : terms.Terms Unit Bytes := symbolic.terms

/-- The bytes of a literal as a Rust byte slice, if they fit one. -/
def toSlice (b : ByteArray) : Option (Slice Std.U8) :=
  if h : b.data.toList.length ≤ Usize.max then
    some (Slice.from (b.data.toList.map fun x => (⟨x.toBitVec⟩ : Std.U8)) (by simpa using h))
  else none

/-- A message carries an item when it is a literal. -/
def messages : client.Messages Unit Bytes Bytes where
  termsTermsInst := dyTerms
  parse _ m := RustM.ok (match Literal.bytesToLiteral m with
    | some b => toSlice b
    | none => none)

/-- A fixed, authenticated historical snapshot with `2^height` leaves. The application supplies
its root, and every stored item has an opening that the production verifier accepts under it. -/
class Snapshot where
  height : Std.U32
  root : Bytes
  items : Std.U64 → Slice Std.U8
  honest : ∀ loc : Std.U64, loc.val < 2^height.val → ∃ ws : Slice Bytes,
    client.verify dyTerms () height loc root (items loc) ws = RustM.ok true

end
end Qmdb
