module
public import Qmdb.Mmb.Peaks

/-! The pinned conversion from physical position to leaf index. The initial estimate stays
below the required crossing. The loop advances one leaf at a time until it finds the
position or passes it. -/

namespace Qmdb.Mmb.Inverse
open Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic.mmb_geometry Peaks
@[expose] public section

/-- MMB position of a leaf. -/
def position (n : Nat) := 2 * n - (n + 1).log2

private theorem log_mono {n m : Nat} (hn : n ≠ 0) (h : n ≤ m) : n.log2 ≤ m.log2 :=
  (Nat.le_log2 (by omega)).mpr (((Nat.le_log2 hn).mp (le_refl _)).trans h)

private theorem enough (n : Nat) : (n + 1).log2 ≤ 2 * n := by
  cases n with
  | zero => decide
  | succ n => have := Nat.log2_le_self (n + 1 + 1); omega

/-- Each new leaf lies strictly beyond its predecessor in physical order. -/
theorem strict : StrictMono position := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := log_mono (n := n + 2) (m := 2 * (n + 1)) (by omega) (by omega)
  rw [Nat.log2_two_mul (by omega)] at h
  unfold position
  have := enough n
  change 2 * n - (n + 1).log2 < 2 * (n + 1) - (n + 2).log2
  omega

private theorem body (p n : Std.U64) (bound : n.val ≤ maxLeaves) :
    ∃ next : Std.U64, next.val = n.val + 1 ∧
      position_to_location_loop.body p n = RustM.ok
        (if position n.val = p.val then ControlFlow.done (.Some n)
         else if p.val < position n.val then .done .None else .cont next) := by
  obtain ⟨d, hd, vd⟩ := mul_ok (2#u64) n (by dsimp [maxLeaves] at bound; scalar_tac)
  obtain ⟨next, hn, vn⟩ := add_ok n 1#u64 (by dsimp [maxLeaves] at bound; scalar_tac)
  change d.val = 2 * n.val at vd
  change next.val = n.val + 1 at vn
  obtain ⟨k, hk, vk⟩ := log_ok next (by omega) (by omega)
  obtain ⟨base, hb, vb⟩ := sub_ok d (UScalar.cast .U64 k)
    (by rw [castUp, vk, vn, vd]; exact enough _)
  rw [castUp, vk, vn, vd] at vb
  change base.val = position n.val at vb
  refine ⟨next, vn, ?_⟩
  have same : base = p ↔ position n.val = p.val :=
    ⟨fun eq => by simpa [eq] using vb.symm,
     fun eq => UScalar.eq_of_val_eq (vb.trans eq)⟩
  simp [position_to_location_loop.body, hd, hn, hk, lift, hb, same, vb]
  split <;> first | rfl | split <;> rfl

private theorem scan (p target n : Std.U64) (bound : target.val ≤ maxLeaves)
    (start : n.val ≤ target.val) (upper : p.val ≤ position target.val)
    (lower : ∀ k, k < target.val → position k < p.val) :
    position_to_location_loop p n =
      RustM.ok (if position target.val = p.val then .Some target else .None) := by
  obtain ⟨next, val, step⟩ := body p n (start.trans bound)
  by_cases last : n.val = target.val
  · obtain rfl := UScalar.eq_of_val_eq last
    apply loop_done
    by_cases eq : position n.val = p.val
    · simpa [eq] using step
    · simpa [eq, show p.val < position n.val by omega] using step
  · have earlier := lower n.val (by omega)
    have again := loop_cont _ _ _ (by
      simpa [show position n.val ≠ p.val by omega,
        show ¬p.val < position n.val by omega] using step)
    exact again.trans (scan p target next bound (by omega) upper lower)
termination_by target.val - n.val
decreasing_by omega

private theorem lookup (p target : Std.U64) (bound : target.val ≤ maxLeaves)
    (upper : p.val ≤ position target.val) (lower : ∀ k, k < target.val → position k < p.val) :
    position_to_location p =
      RustM.ok (if position target.val = p.val then .Some target else .None) := by
  obtain ⟨half, half_eq, half_val⟩ := UScalar.div_spec p (y := 2#u64) (by decide)
  change half.val = p.val / 2 at half_val
  have half_le : half.val ≤ target.val := by unfold position at upper; omega
  obtain ⟨n, hn, vn⟩ := add_ok half 1#u64 (by dsimp [maxLeaves] at bound; scalar_tac)
  change n.val = half.val + 1 at vn
  obtain ⟨k, hk, vk⟩ := log_ok n (by omega) (by omega)
  have log_le := log_mono (n := n.val) (m := target.val + 1) (by omega) (by omega)
  have fits : p.val + (UScalar.cast .U64 k).val ≤ 2 * target.val := by
    rw [castUp, vk]
    have := enough target.val
    unfold position at upper
    omega
  obtain ⟨total, ht, vt⟩ := add_ok p (UScalar.cast .U64 k)
    (by dsimp [maxLeaves] at bound; scalar_tac)
  obtain ⟨start, hs, vs⟩ := UScalar.div_spec total (y := 2#u64) (by decide)
  change start.val = total.val / 2 at vs
  simpa [position_to_location, half_eq, hn, hk, lift, ht, hs] using
    scan p target start bound (by omega) upper lower

/-- A valid physical leaf position inverts to exactly its original location. -/
theorem leaf (p n : Std.U64) (bound : n.val ≤ maxLeaves) (pos : p.val = position n.val) :
    position_to_location p = RustM.ok (.Some n) := by
  simpa [pos] using lookup p n bound (by omega)
    (fun k hk => pos ▸ strict hk)

/-- A position strictly between consecutive leaves is an internal node. -/
theorem gap (p n : Std.U64) (bound : n.val + 1 ≤ maxLeaves)
    (below : position n.val < p.val) (above : p.val < position (n.val + 1)) :
    position_to_location p = RustM.ok .None := by
  obtain ⟨next, _, v⟩ := add_ok n 1#u64 (by dsimp [maxLeaves] at bound; scalar_tac)
  change next.val = n.val + 1 at v
  have lt : p.val < position next.val := v ▸ above
  simpa [Nat.ne_of_gt lt] using lookup p next (by omega) lt.le
    (fun k hk => (strict.monotone (by omega : k ≤ n.val)).trans_lt below)

end
end Qmdb.Mmb.Inverse
