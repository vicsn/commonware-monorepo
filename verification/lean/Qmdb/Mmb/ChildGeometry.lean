module
public import Qmdb.Mmb.Peaks

/-! The pinned delayed-merge arithmetic at each reachable interior node. -/

namespace Qmdb.Mmb.Peaks
open Aeneas Aeneas.Std Commonware.Symbolic commonware_symbolic.mmb_geometry
@[expose] public section

/-- Unfold the delayed birth of a non-leaf subtree. -/
theorem birth_succ (start k : Nat) : birth start (k + 1) = start + 3 * 2 ^ k - 2 := by
  have := Nat.two_pow_pos k
  simp [birth, pow_succ]
  omega

/-- A peak or descendant with a valid birth inside the snapshot and an aligned first leaf. -/
structure Subtree (n start height : Nat) : Prop where
  /-- Upper bound accepted by the pinned family. -/
  valid : n ≤ maxLeaves
  /-- Machine shifts fit. -/
  heightBound : height ≤ 62
  /-- A perfect subtree starts at a multiple of its width. -/
  aligned : 2 ^ height ∣ start
  /-- The node has already been appended. -/
  born : birth start height < n

/-- The next root enumerated by the peak iterator is a reachable subtree. -/
theorem cursor_subtree {it : Peaks} {n start i : Nat} (valid : n ≤ maxLeaves)
    (c : Cursor it n (i + 1) start) : Subtree n start (peakHeight (n + 1) i) := by
  have height : peakHeight (n + 1) i ≤ i + 1 := by dsimp [peakHeight]; omega
  refine ⟨valid, le_trans height (le_trans c.limit (logBound (by omega))), ?_,
    birth_inside c.extent⟩
  exact dvd_trans (pow_dvd_pow 2 height) c.aligned

private theorem selected_aux {n k : Nat} (valid : n ≤ maxLeaves) {it : Peaks}
    {start i loc peak h off : Nat} (c : Cursor it n k start)
    (selected : containing (peakHeights (n + 1) k) i loc = some (peak, h, off)) :
    off ≤ loc ∧ Subtree n (start + loc - off) h := by
  induction k generalizing it start i loc with
  | zero => simp [peakHeights, containing] at selected
  | succ k ih =>
    simp only [peakHeights, containing] at selected
    split at selected
    · cases selected
      exact ⟨le_refl _, by simpa using cursor_subtree valid c⟩
    · next outside =>
      obtain ⟨_, _, _, _, height, _, rest⟩ := next_peak valid c
      rw [height] at rest
      obtain ⟨within, tree⟩ := ih rest selected
      exact ⟨within.trans (Nat.sub_le _ _), by convert tree using 1; omega⟩

/-- A successful peak selection gives the physical-child invariant at the DFS root. -/
theorem containing_subtree (n : Std.U64) (valid : n.val ≤ maxLeaves) {loc peak h off : Nat}
    (selected : containing (heights n.val) 0 loc = some (peak, h, off)) :
    Subtree n.val (loc - off) h := by
  obtain ⟨_, _, c⟩ := initialized n valid
  simpa using (selected_aux valid c selected).2

/-- Delayed child birth locations computed by the pinned Rust function. -/
theorem child_leaves_ok (start k : Nat) (b : Std.U64) (h : Std.U32)
    (height : h.val = k + 1) (small : h.val ≤ 62) (parent : b.val = birth start (k + 1)) :
    ∃ l r, child_leaves b h = RustM.ok (l, r) ∧
      l.val = birth start k ∧ r.val = birth (start + 2 ^ k) k := by
  rw [birth_succ] at parent
  cases k with
  | zero =>
    have one : h = 1#u32 := UScalar.eq_of_val_eq height
    simp at parent
    obtain ⟨l, hl, vl⟩ := sub_ok b 1#u64 (by scalar_tac)
    exact ⟨l, b, by simp [child_leaves, one, hl], by simp [birth, vl, parent],
      by simp [birth, parent]⟩
  | succ k =>
    have ne : h ≠ 1#u32 := by rintro rfl; scalar_tac
    obtain ⟨j, hj, vj⟩ := sub_ok h 2#u32 (by scalar_tac)
    have idx : j.val = k := by scalar_tac
    obtain ⟨w, hw, vw⟩ := pow_ok j (by omega)
    rw [idx] at vw
    have limit := Nat.pow_le_pow_right (n := 2) (by decide) (show k ≤ 60 by omega)
    obtain ⟨t, ht, vt⟩ := mul_ok 3#u64 w (by scalar_tac)
    have positive := Nat.two_pow_pos k
    change t.val = 3 * w.val at vt
    rw [pow_succ] at parent
    obtain ⟨l, hl, vl⟩ := sub_ok b t (by omega)
    obtain ⟨r, hr, vr⟩ := sub_ok b w (by omega)
    exact ⟨l, r, by simp [child_leaves, ne, hj, hw, ht, hl, hr],
      by rw [birth_succ]; omega, by rw [birth_succ, pow_succ]; omega⟩

/-- Both children preserve alignment and have been born whenever the parent has. -/
theorem Subtree.children {n s k : Nat} (parent : Subtree n s (k + 1)) :
    Subtree n s k ∧ Subtree n (s + 2 ^ k) k := by
  have aligned := dvd_trans (pow_dvd_pow 2 (show k ≤ k + 1 by omega)) parent.aligned
  have near := parent.born
  rw [birth_succ] at near
  have left : birth s k < n ∧ birth (s + 2 ^ k) k < n := by
    cases k with
    | zero => simp [birth] at *; omega
    | succ k =>
      have := Nat.two_pow_pos k
      rw [pow_succ] at near
      rw [birth_succ, birth_succ, pow_succ]
      omega
  exact ⟨⟨parent.valid, le_trans (by omega) parent.heightBound, aligned, left.1⟩,
    ⟨parent.valid, le_trans (by omega) parent.heightBound, dvd_add aligned (dvd_refl _), left.2⟩⟩

/-- A non-leaf's birth cannot be the insertion just before an MMB size power-of-two boundary. -/
theorem birth_not_boundary {s k : Nat} (aligned : 2 ^ (k + 1) ∣ s) :
    ∀ i, 2 ^ i ≠ birth s (k + 1) + 2 := by
  obtain ⟨q, rfl⟩ := aligned
  intro i equal
  have width := Nat.two_pow_pos k
  have factor : 2 ^ i = 2 ^ k * (2 * q + 3) := by
    rw [birth_succ, pow_succ] at equal
    rw [Nat.mul_add, ← Nat.mul_assoc]
    omega
  have divides : 2 * q + 3 ∣ 2 ^ i := by rw [factor]; exact dvd_mul_left _ _
  obtain ⟨t, _, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp divides
  cases t with
  | zero => simp at ht
  | succ t => rw [pow_succ] at ht; omega

/-- An aligned parent lies in the one-position gap between consecutive leaf positions. -/
theorem parent_log {s k : Nat} (aligned : 2 ^ (k + 1) ∣ s) :
    (birth s (k + 1) + 2).log2 = (birth s (k + 1) + 1).log2 := by
  let b := birth s (k + 1)
  have lo := Nat.log2_self_le (n := b + 1) (by omega)
  have hi := Nat.lt_log2_self (n := b + 1)
  change (b + 2).log2 = (b + 1).log2
  apply (Nat.log2_eq_iff (n := b + 2) (by omega)).mpr
  exact ⟨by omega, by
    have no := birth_not_boundary aligned ((b + 1).log2 + 1)
    change 2 ^ ((b + 1).log2 + 1) ≠ b + 2 at no
    omega⟩

end
end Qmdb.Mmb.Peaks
