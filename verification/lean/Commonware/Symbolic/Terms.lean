module
public import Commonware.Symbolic.Hashing
public import DY.EquationalTheory.Hash
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.Literal

/-! The extracted Rust read in DyLean, for any term algebra that includes DyLean's literals,
concatenation and hashing. Each target fixes its algebra with `#combine`; this reading applies to
every algebra that has these three constructors.

Trusted: `hashing` reads production hash inputs as terms (byte parts as literals, parts
concatenated to the right) under any hash on terms, `symbolic` is that reading with DyLean's hash
constructor, and `messages` reads the item of a received message as the bytes of a literal.
Checked: the lemmas, which show that the reading keeps byte parts and concatenations apart and
that DyLean's hash has no collisions. -/

namespace Commonware.Symbolic
open DY Aeneas Aeneas.Std CoreModels commonware_symbolic
@[expose] public section

/-- The bytes of a Rust byte slice. -/
def toByteArray (s : Slice Std.U8) : ByteArray :=
  ⟨(s.val.map fun b => UInt8.ofNat b.val).toArray⟩

/-- The bytes of a literal as a Rust byte slice, if they fit one. -/
def toSlice (b : ByteArray) : Option (Slice Std.U8) :=
  if h : b.data.toList.length ≤ Usize.max then
    some (Slice.from (b.data.toList.map fun x => (⟨x.toBitVec⟩ : Std.U8)) (by simpa using h))
  else none

theorem toByteArray_inj {a b : Slice Std.U8} (h : toByteArray a = toByteArray b) : a = b := by
  apply Slice.ext
  have lists : a.val.map (fun x => UInt8.ofNat x.val) = b.val.map (fun x => UInt8.ofNat x.val) := by
    have := congrArg ByteArray.data h
    simpa [toByteArray] using this
  refine List.map_injective_iff.mpr ?_ lists
  intro x y same
  apply UScalar.eq_of_val_eq
  have hx : x.val < 256 := by scalar_tac
  have hy : y.val < 256 := by scalar_tac
  have := congrArg UInt8.toNat same
  simp at this
  omega

theorem toSlice_toByteArray (s : Slice Std.U8) : toSlice (toByteArray s) = some s := by
  have fits := s.property
  have same : (s.val.map fun b => UInt8.ofNat b.val).map (fun x => (⟨x.toBitVec⟩ : Std.U8)) =
      s.val := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id s.val]
    apply List.map_congr_left
    intro b _
    apply UScalar.eq_of_val_eq
    change (BitVec.ofNat 8 b.val).toNat = b.val
    have : b.val < 2^8 := by scalar_tac
    simp
  have short : (toByteArray s).data.toList.length ≤ Usize.max := by simp [toByteArray]
  unfold toSlice
  simp only [short, ↓reduceDIte]
  congr 1
  apply Slice.ext
  simpa [Slice.from_val, toByteArray] using same

variable [BytesFunctor] [BytesFunctor.Has Literal.SubF]

/-! ## Literals -/

/-- A hash-input part as a term. -/
def part : terms.Part Bytes → Bytes
  | .Bytes s => Literal.literalToBytes (toByteArray s)
  | .Digest d => d

theorem part_bytes_inj {a b : Slice Std.U8}
    (h : part (.Bytes a) = (part (.Bytes b) : Bytes)) : a = b := by
  apply toByteArray_inj
  simpa only [part, Literal.bytesToLiteral_literalToBytes, Option.some.injEq] using
    congrArg (Literal.bytesToLiteral (Bytes := Bytes)) h

/-- A message carries an item when it is a literal. -/
def messages : client.Messages Unit Bytes where
  parse _ m := RustM.ok (match Literal.bytesToLiteral m with
    | some b => toSlice b
    | none => none)

/-- A message carrying `item` as a literal. -/
def carrying (item : Slice Std.U8) : Bytes := Literal.literalToBytes (toByteArray item)

theorem parse_carrying (item : Slice Std.U8) :
    messages.parse () (carrying item) = RustM.ok (some item) := by
  simp [messages, carrying, Literal.bytesToLiteral_literalToBytes, toSlice_toByteArray]

/-! ## Hash inputs -/

variable [BytesFunctor.Has Concat.SubF] [BytesFunctor.Has Hash.SubF] [BytesLength]

/-- Parts concatenated to the right. -/
def chain : List (terms.Part Bytes) → Bytes
  | [] => Literal.literalToBytes ByteArray.empty
  | [p] => part p
  | p :: rest => Concat.concat (part p) (chain rest)

/-- Hashing with `hash` over the concatenated parts. `hash` is any function on terms, so it may
collide. -/
def hashing (hash : Bytes → Bytes) : Scheme Bytes Bytes where
  hash := hash
  encode := chain

/-- Symbolic hashing: DyLean's hash constructor over the concatenated parts. -/
def symbolic : Scheme Bytes Bytes := hashing Hash.hash

/-- The production hash inputs as DyLean terms. -/
abbrev dyTerms : terms.Terms Unit Bytes := symbolic.terms

omit [BytesFunctor.Has Literal.SubF] [BytesFunctor.Has Hash.SubF] in
theorem concat_inj {a b c d : Bytes} (h : Concat.concat a b = Concat.concat c d) :
    a = c ∧ b = d := by
  simp only [Concat.concat] at h
  grind

/-- DyLean's hash constructor has no collisions. -/
theorem no_collision (x y : Bytes) : ¬ symbolic.Collision x y :=
  fun clash => clash.1 (Hash.hash_inj _ _ clash.2)

end
end Commonware.Symbolic
