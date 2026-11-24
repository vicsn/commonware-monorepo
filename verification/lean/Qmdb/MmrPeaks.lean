module
public import Qmdb.Reconstruct

/-! The peaks of an MMR whose leaf count is a power of two, as the production MMR geometry yields
them: one peak, at the last position of its perfect tree. Checked by Lean. -/

namespace Qmdb.MmrPeaks
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic Qmdb.Reconstruct
@[expose] public section

/-- The production read of the next MMR peak. -/
abbrev next := mmr_geometry.Peaks.Insts.Commonware_symbolicReconstructPeaks.next

/-- The bit test of the extracted loop: bit `i` of `leaves`. -/
theorem bit_ok (leaves : Std.U64) (i : Std.U32) (small : i.val < 64) :
    ∃ z : Std.U64, leaves >>> i = RustM.ok z ∧
      ((z &&& 1#u64) = 1#u64 ↔ leaves.val.testBit i.val = true) := by
  obtain ⟨z, hz, zv, -, -⟩ := ok_of_partialSpec (UScalar.ShiftRight_spec leaves i)
    (by intro e; cases e <;> simp; omega) (by simp)
  refine ⟨z, hz, ?_⟩
  constructor
  · intro one
    have v := congrArg UScalar.val one
    rw [UScalar.val_and, zv] at v
    simp only [Nat.testBit, Nat.and_comm] at v ⊢
    simp at v ⊢
    omega
  · intro set
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and, zv]
    simp only [show (1#u64 : Std.U64).val = 1 from rfl]
    rw [Nat.and_one_is_mod]
    simp only [Nat.testBit, Nat.one_and_eq_mod_two] at set
    simp at set ⊢
    omega

/-- Scanning bits below `j` that are all clear finds no peak. -/
theorem scan_none (leaves nodes : Std.U64) (j : Nat) :
    (∀ i < j, leaves.val.testBit i = false) → j ≤ 64 → ∀ height : Std.U32, height.val = j →
      mmr_geometry.Peaks.next_loop ⟨leaves, height, nodes⟩ =
        RustM.ok (.None, leaves, 0#u32, nodes) := by
  induction j with
  | zero =>
    intro _ _ height hv
    have zero : height = 0#u32 := UScalar.eq_of_val_eq (by simp [hv])
    subst zero
    have step : mmr_geometry.Peaks.next_loop.body ⟨leaves, 0#u32, nodes⟩ =
        RustM.ok (.done (.None, leaves, 0#u32, nodes)) := by
      simp [mmr_geometry.Peaks.next_loop.body]
    unfold mmr_geometry.Peaks.next_loop
    exact loop_done _ _ _ step
  | succ j ih =>
    intro clear bound height hv
    have pos : height > 0#u32 := by scalar_tac
    obtain ⟨i, hi, iv⟩ := sub_ok height 1#u32 (by scalar_tac)
    have iv' : i.val = j := by simp at iv; omega
    obtain ⟨z, hz, bit⟩ := bit_ok leaves i (by omega)
    have notSet : ¬ (z &&& 1#u64) = 1#u64 := by
      rw [bit, iv']; simp [clear j (by omega)]
    have step : mmr_geometry.Peaks.next_loop.body ⟨leaves, height, nodes⟩ =
        RustM.ok (.cont ⟨leaves, i, nodes⟩) := by
      simp [mmr_geometry.Peaks.next_loop.body, pos, hi, hz, Std.lift, notSet]
    unfold mmr_geometry.Peaks.next_loop
    rw [loop_cont _ _ _ step]
    exact ih (fun i hi => clear i (by omega)) (by omega) i iv'

/-- Scanning down from above the highest set bit `h` finds the peak of height `h`. -/
theorem scan_found (leaves nodes : Std.U64) (h : Nat) (set : leaves.val.testBit h = true)
    (low : h ≤ 62) (fits : nodes.val + 2 ^ (h + 1) ≤ 2 ^ 63) (k : Nat) :
    (∀ i, h < i → i < h + 1 + k → leaves.val.testBit i = false) → h + 1 + k ≤ 64 →
    ∀ height : Std.U32, height.val = h + 1 + k →
      ∃ (peak next : Std.U64) (hh : Std.U32),
        mmr_geometry.Peaks.next_loop ⟨leaves, height, nodes⟩ =
          RustM.ok (.Some (peak, hh), leaves, hh, next) ∧
        peak.val = nodes.val + 2 ^ (h + 1) - 2 ∧ hh.val = h ∧
        next.val = nodes.val + 2 ^ (h + 1) - 1 := by
  have one : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
  induction k with
  | zero =>
    intro _ _ height hv
    have pos : height > 0#u32 := by scalar_tac
    obtain ⟨i, hi, iv⟩ := sub_ok height 1#u32 (by scalar_tac)
    have iv' : i.val = h := by simp at iv; omega
    obtain ⟨z, hz, bit⟩ := bit_ok leaves i (by omega)
    have isSet : (z &&& 1#u64) = 1#u64 := by rw [bit, iv']; exact set
    obtain ⟨i3, hi3, i3v⟩ := add_ok i 1#u32 (by scalar_tac)
    obtain ⟨w, hw, wv⟩ := pow_ok i3 (by simp at i3v; omega)
    have wv' : w.val = 2 ^ (h + 1) := by rw [wv]; simp at i3v; rw [i3v, iv']
    obtain ⟨size, hsize, sizev⟩ := sub_ok w 1#u64 (by simp; omega)
    obtain ⟨i5, hi5, i5v⟩ := add_ok nodes size (by simp at sizev; scalar_tac)
    obtain ⟨peak, hpeak, peakv⟩ := sub_ok i5 1#u64 (by simp at sizev i5v ⊢; omega)
    refine ⟨peak, i5, i, ?_, by simp at sizev i5v peakv; omega, iv',
      by simp at sizev i5v; omega⟩
    have step : mmr_geometry.Peaks.next_loop.body ⟨leaves, height, nodes⟩ =
        RustM.ok (.done (.Some (peak, i), leaves, i, i5)) := by
      simp [mmr_geometry.Peaks.next_loop.body, pos, hi, hz, Std.lift, isSet, hi3, hw, hsize,
        hi5, hpeak]
    unfold mmr_geometry.Peaks.next_loop
    exact loop_done _ _ _ step
  | succ k ih =>
    intro clear bound height hv
    have pos : height > 0#u32 := by scalar_tac
    obtain ⟨i, hi, iv⟩ := sub_ok height 1#u32 (by scalar_tac)
    have iv' : i.val = h + 1 + k := by simp at iv; omega
    obtain ⟨z, hz, bit⟩ := bit_ok leaves i (by omega)
    have notSet : ¬ (z &&& 1#u64) = 1#u64 := by
      rw [bit, iv']; simp [clear (h + 1 + k) (by omega) (by omega)]
    have step : mmr_geometry.Peaks.next_loop.body ⟨leaves, height, nodes⟩ =
        RustM.ok (.cont ⟨leaves, i, nodes⟩) := by
      simp [mmr_geometry.Peaks.next_loop.body, pos, hi, hz, Std.lift, notSet]
    unfold mmr_geometry.Peaks.next_loop
    rw [loop_cont _ _ _ step]
    exact ih (fun j lo hi' => clear j lo (by omega)) (by omega) i iv'

/-- An MMR of `2 ^ h` leaves has one peak, at position `2 ^ (h + 1) - 2`, of height `h`. -/
theorem single_peak (h : Nat) (low : h ≤ 62) (leaves : Std.U64) (lv : leaves.val = 2 ^ h) :
    ∃ (st : mmr_geometry.Peaks) (pos : Std.U64) (hh : Std.U32),
      mmr_geometry.Peaks.new leaves = RustM.ok st ∧ pos.val = 2 ^ (h + 1) - 2 ∧ hh.val = h ∧
      Yields next st [(pos, hh)] := by
  have set : leaves.val.testBit h = true := by rw [lv, Nat.testBit_two_pow]; simp
  have above : ∀ i, h < i → leaves.val.testBit i = false := by
    intro i hi; rw [lv, Nat.testBit_two_pow]; simp; omega
  have below : ∀ i < h, leaves.val.testBit i = false := by
    intro i hi; rw [lv, Nat.testBit_two_pow]; simp; omega
  have pow : 2 ^ (h + 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨peak, size, hh, run, peakv, hhv, sizev⟩ := scan_found leaves 0#u64 h set low
    (by simp; omega) (63 - h) (fun i lo _ => above i lo) (by omega) (core.num.U64.BITS)
    (by simp [core.num.U64.BITS]; omega)
  have first : next ⟨leaves, core.num.U64.BITS, 0#u64⟩ =
      RustM.ok (.Some (peak, hh), ⟨leaves, hh, size⟩) := by
    simp [next, mmr_geometry.Peaks.Insts.Commonware_symbolicReconstructPeaks.next,
      mmr_geometry.Peaks.next, run]
  have rest := scan_none leaves size h below (by omega) hh hhv
  have second : next ⟨leaves, hh, size⟩ = RustM.ok (.None, ⟨leaves, 0#u32, size⟩) := by
    simp [next, mmr_geometry.Peaks.Insts.Commonware_symbolicReconstructPeaks.next,
      mmr_geometry.Peaks.next, rest]
  refine ⟨⟨leaves, core.num.U64.BITS, 0#u64⟩, peak, hh, by simp [mmr_geometry.Peaks.new],
    by simp at peakv; omega, hhv, .cons first (.nil second)⟩

end
end Qmdb.MmrPeaks
