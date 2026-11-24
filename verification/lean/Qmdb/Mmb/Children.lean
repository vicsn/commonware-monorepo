module
public import Qmdb.Mmb.ChildGeometry
public import Qmdb.Mmb.Inverse

/-! The pinned physical child lookup computes both positions used by the symbolic DFS, for
the peaks it starts from and all recursively reachable descendants. -/

namespace Qmdb.Mmb.Peaks
open Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic.mmb_geometry
@[expose] public section

private theorem pos_eq (s k : Nat) :
    subtreePosition s k =
      Inverse.position (birth s k) + (if k = 0 then 0 else 1) := rfl

private theorem parent_lookup {n s k : Nat} (tree : Subtree n s (k + 1))
    (p b : Std.U64) (node : p.val = subtreePosition s (k + 1)) (loc : b.val = birth s (k + 1)) :
    parent_birth_leaf p = RustM.ok (.Some b) := by
  have pos : p.val = Inverse.position b.val + 1 := by simpa [pos_eq, loc] using node
  have bounds : b.val + 1 ≤ maxLeaves := by
    have := tree.born
    have := tree.valid
    omega
  have stable : (b.val + 2).log2 = (b.val + 1).log2 := by rw [loc]; exact parent_log tree.aligned
  have positive : 0 < b.val := by
    have := Nat.two_pow_pos k
    rw [loc, birth_succ]
    omega
  have start : ¬p < 2#u64 := by
    have monotone := Inverse.strict (show 0 < b.val by omega)
    change 0 < Inverse.position b.val at monotone
    scalar_tac
  have enough := Nat.log2_le_self (b.val + 1)
  have no := Inverse.gap p b bounds (by omega) (by
    rw [pos]
    simp only [Inverse.position]
    change 2 * b.val - (b.val + 1).log2 + 1 < 2 * (b.val + 1) - (b.val + 2).log2
    omega)
  obtain ⟨prev, hp, vp⟩ := sub_ok p 1#u64 (by scalar_tac)
  have yes := Inverse.leaf prev b (by omega) (by change prev.val = p.val - 1 at vp; omega)
  simp [parent_birth_leaf, start, no, CoreModels.core.option.Option.is_some, hp, yes]

/-- Actual results of the pinned Rust children function, in left-to-right order. The
subtrees retain the premises required to repeat the argument at each internal node. -/
theorem physical_children {n s k : Nat} (tree : Subtree n s (k + 1)) (p : Std.U64) (h : Std.U32)
    (position : p.val = subtreePosition s (k + 1)) (height : h.val = k + 1) :
    ∃ left right, commonware_symbolic.mmb_geometry.children p h = RustM.ok (left, right) ∧
      left.val = subtreePosition s k ∧ right.val = subtreePosition (s + 2 ^ k) k ∧
      Subtree n s k ∧ Subtree n (s + 2 ^ k) k := by
  let b : Std.U64 := ⟨BitVec.ofNat 64 (birth s (k + 1))⟩
  have room := tree.born
  have valid := tree.valid
  have loc : b.val = birth s (k + 1) := by
    change birth s (k + 1) % 2 ^ 64 = _
    apply Nat.mod_eq_of_lt
    dsimp [maxLeaves] at valid
    omega
  have found := parent_lookup tree p b position loc
  obtain ⟨l, r, child, vl, vr⟩ := child_leaves_ok s k b h height (height ▸ tree.heightBound) loc
  obtain ⟨lt, rt⟩ := tree.children
  have zero : h = 1#u32 ↔ k = 0 := by
    exact ⟨fun eq => by rw [eq] at height; scalar_tac,
      fun eq => UScalar.eq_of_val_eq (by simp_all)⟩
  obtain ⟨lp, left, pl⟩ := birth_position l (decide (h = 1#u32)) (by
    have := lt.born; omega)
  obtain ⟨rp, right, pr⟩ := birth_position r (decide (h = 1#u32)) (by
    have := rt.born; omega)
  have hn : h > 0#u32 := by scalar_tac
  refine ⟨lp, rp, ?_, ?_, ?_, lt, rt⟩
  · simp [commonware_symbolic.mmb_geometry.children, hn, found, CoreModels.core.option.Option.expect,
      child, left, right]
  · simpa [pos_eq, Inverse.position, zero, vl] using pl
  · simpa [pos_eq, Inverse.position, zero, vr] using pr

end
end Qmdb.Mmb.Peaks
