module
public import Commonware.Symbolic.Terms

/-! Fixed-width big-endian words and their symbolic wire literals. -/

namespace Commonware.Symbolic
open DY
@[expose] public section

/-- Bytes in serialization order. -/
abbrev Wire (n : Nat) := Vector UInt8 n

/-- Write the least significant byte last, as in Rust's `to_be_bytes`. -/
def writeBE : (n : Nat) → BitVec (8 * n) → Wire n
  | 0, _ => #v[]
  | n + 1, x => (writeBE n (x.extractLsb' 8 (8 * n))).push
      ⟨x.extractLsb' 0 8⟩

/-- Read an unsigned big-endian word of the given width. -/
def readBE : (n : Nat) → Wire n → BitVec (8 * n)
  | 0, _ => 0
  | n + 1, xs => readBE n xs.pop ++ xs.back.toBitVec

@[simp] theorem read_write (n : Nat) (x : BitVec (8 * n)) : readBE n (writeBE n x) = x := by
  induction n with
  | zero =>
    apply BitVec.eq_of_getElem_eq
    simp
  | succ n ih =>
    simp [readBE, writeBE, ih, Vector.back]

@[simp] theorem write_read (n : Nat) (xs : Wire n) : writeBE n (readBE n xs) = xs := by
  induction n with
  | zero =>
    apply Vector.ext
    simp
  | succ n ih =>
    simp [readBE, writeBE, BitVec.extractLsb'_append_eq_left,
      BitVec.extractLsb'_append_eq_right, ih]

/-- DyLean literal carrying a fixed-width wire value. -/
def wireLiteral [BytesFunctor] [BytesFunctor.Has Literal.SubF] (w : Wire n) : Bytes :=
  Literal.literalToBytes ⟨w.toArray⟩

theorem wireLiteral_injective [BytesFunctor] [BytesFunctor.Has Literal.SubF] {a b : Wire n}
    (h : wireLiteral a = wireLiteral b) : a = b := by
  have same := congrArg (Literal.bytesToLiteral (Bytes := Bytes)) h
  simp only [wireLiteral, Literal.bytesToLiteral_literalToBytes, Option.some.injEq] at same
  exact Vector.toArray_inj.mp (congrArg ByteArray.data same)

@[simp] theorem wireLiteral_length [BytesFunctor] [BytesFunctor.Has Literal.SubF] [BytesLength]
    [BytesLength.Has Literal.SubF.length] (w : Wire n) : Bytes.length (wireLiteral w) = n := by
  simp [wireLiteral, ByteArray.size]

end
end Commonware.Symbolic
