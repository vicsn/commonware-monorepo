module
public import Qmdb.Active
public import Qmdb.Verifier

/-! The fixed-width bitmap check agrees with the activity arithmetic extracted from Rust. -/

namespace Qmdb.Active
open Aeneas Aeneas.Std Commonware.Symbolic commonware_symbolic
@[expose] public section

/-- The Rust offset is total for Tempo's 32-byte chunks. -/
theorem offset_ok (loc : Std.U64) :
    ∃ offset, activity.offset loc 256#u64 = RustM.ok offset ∧ offset.val = loc.val % 256 :=
  ok_of_spec (UScalar.rem_spec loc (y := 256#u64) (by decide))

/-- The Rust mask tests the little-endian bit within the byte. -/
theorem mask_ok (byte : UInt8) (offset : Std.U64) :
    activity.is_set ⟨byte.toBitVec⟩ offset = RustM.ok
      (byte &&& (1 <<< UInt8.ofNat (offset.val % 8)) != 0) := by
  obtain ⟨shift, hs, hv⟩ := ok_of_spec (UScalar.rem_spec offset (y := 8#u64) (by decide))
  change shift.val = offset.val % 8 at hv
  have bound : shift.val < 8 := by omega
  obtain ⟨mask, hm, _, hb, _⟩ := ok_of_partialSpec (UScalar.ShiftLeft_spec (1#u8) shift _ rfl)
    (by intro e; cases e <;> simp; omega) (by simp)
  simp [activity.is_set, hs, hm]
  let mask8 : BitVec 8 := mask.bv
  simp [lift]
  congr 1
  apply congrArg (@UScalar.mk .U8)
  change byte.toBitVec &&& mask8 = byte.toBitVec &&& (1 <<< UInt8.ofNat (offset.val % 8)).toBitVec
  have same : mask8 = (1 : BitVec 8) <<< shift.val := hb
  rw [same, hv, UInt8.toBitVec_shiftLeft]
  congr 1
  simp

/-- A fixed 32-byte chunk as the byte slice seen by Rust. -/
def Chunk.asSlice (chunk : Chunk) : Slice Std.U8 :=
  Slice.from (chunk.toList.map fun b => ⟨b.toBitVec⟩) (by simp; scalar_tac)

/-- Call the extracted production bitmap check, including the cast and slice access. -/
def rustActive (chunk : Chunk) (loc : Std.U64) : RustM Bool :=
  activity.get (Chunk.asSlice chunk) loc 256#u64

/-- The extracted check returns the set bit for every 64-bit location, including at either
end of a chunk. The cast to usize is in bounds on each supported machine width. -/
theorem rustActive_eq (chunk : Chunk) (loc : Std.U64) :
    rustActive chunk loc = RustM.ok (activeBit chunk loc.val) := by
  obtain ⟨offset, ho, hv⟩ := offset_ok loc
  obtain ⟨i, hd, hi⟩ := UScalar.div_spec offset (y := 8#u64) (by decide)
  change i.val = offset.val / 8 at hi
  have bound : i.val < 32 := by omega
  have castEq : (UScalar.cast .Usize i).val = i.val := by
    simp [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    cases System.Platform.numBits_eq <;> simp [*] <;> omega
  have room : (UScalar.cast .Usize i).val < (Chunk.asSlice chunk).length := by
    simpa [castEq, Chunk.asSlice, Slice.length, Slice.from_val] using bound
  simp [rustActive, activity.get, ho, hd, lift, Verifier.index_ok _ _ room]
  simp [Chunk.asSlice, Slice.from_val, mask_ok, hi, hv, activeBit]
  have small : loc.val % 256 / 8 < 2 ^ System.Platform.numBits := by
    cases System.Platform.numBits_eq <;> simp [*] <;> omega
  simp only [Nat.mod_eq_of_lt small]

/-- The byte and bit indices used by Tempo's pinned bitmap helper have the same semantics. -/
theorem pinned_eq (chunk : Chunk) (loc : Nat) :
    (chunk[((loc / 8) % 32)]'(by omega) &&& (1 <<< UInt8.ofNat (loc % 8)) != 0) =
      activeBit chunk loc := by
  have idx : loc / 8 % 32 = loc % 256 / 8 := by omega
  simp [activeBit, idx]

end
end Qmdb.Active
