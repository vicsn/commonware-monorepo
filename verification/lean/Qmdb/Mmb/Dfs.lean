module
public import Qmdb.Mmb.Pinned
public import Qmdb.Mmb.Plan
public import Qmdb.Verifier

/-! Refinement of the pinned verifier's left-first DFS to the single-operation shape.
The symbolic backend records the order of sibling, operation and child hash inputs. -/

namespace Qmdb.Mmb.Dfs
open Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic pinned_dfs
@[expose] public section

/-- Record the symbolic sibling references by copying their hash programs. -/
def digest : Digest Shape := ⟨⟨⟨RustM.ok, fun _ x => RustM.ok x⟩⟩⟩

/-- Symbolic leaf and node hashing, indexed by the source subtree's first leaf and height. -/
def hasher : Hasher Bool Shape where
  DigestInst := digest
  leaf_digest _ p _ := RustM.ok (.hash (.pair (.atom (.word (subtreePosition p.1.val 0)))
    (.atom .item)))
  node_digest g p l r :=
    let node := Shape.hash (.pair (.atom (.word (subtreePosition p.1.val p.2.val))) (.pair l r))
    RustM.ok (if g && decide (p.2.val = 8) then .hash (.pair (.atom .bitmap) node) else node)

/-- One subtree passed to the extracted traversal. -/
def tree (start : Std.U64) (height : Std.U32) : Subtree :=
  ⟨(start, height), height, start⟩

/-- The source recursion, with an iterator containing at most one encoded operation. -/
abbrev run := Subtree.reconstruct_digest digest hasher Verifier.single Verifier.element

private theorem outside_eq (s : Std.U64) (h : Std.U32) (r : CoreModels.core.ops.range.Range Std.U64)
    (height : h.val ≤ 63) (fits : s.val + 2 ^ h.val ≤ UScalar.max .U64) :
    (tree s h).is_outside r =
      RustM.ok (decide (s.val + 2 ^ h.val ≤ r.start.val ∨ r.end.val ≤ s.val)) := by
  obtain ⟨width, hw, wv⟩ := pow_ok h height
  obtain ⟨stop, hs, sv⟩ := add_ok s width (by omega)
  simp [tree, Subtree.is_outside, Subtree.is_before, Subtree.leaf_end, hw, hs]
  split <;> rename_i cond <;> simp_all

private theorem outside (g : Bool) (s : Std.U64) (h : Std.U32)
    (r : CoreModels.core.ops.range.Range Std.U64)
    (es : qmdb.Single) (ds : Slice Shape) (c : Std.Usize) (room : c.val < ds.length)
    (height : h.val ≤ 63) (fits : s.val + 2 ^ h.val ≤ UScalar.max .U64)
    (out : s.val + 2 ^ h.val ≤ r.start.val ∨ r.end.val ≤ s.val) :
    ∃ next : Std.Usize, run (tree s h) g r es ds c =
      RustM.ok (.Ok ds.val[c.val], es, next) ∧ next.val = c.val + 1 := by
  obtain ⟨next, eq, known⟩ := succ_ok c ds room
  refine ⟨next, ?_, known⟩
  have bound : c.val < ds.val.length := room
  unfold run
  rw [Subtree.reconstruct_digest.eq_def, outside_eq _ _ _ height fits]
  simp [out, CoreModels.core.slice.Slice.get, core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_index,
    Verifier.index_ok ds c room, bound, core.option.OptionShared0T.copied, eq]

private theorem leaf (g : Bool) (s : Std.U64) (r : CoreModels.core.ops.range.Range Std.U64)
    (item : Slice Std.U8) (ds : Slice Shape) (c : Std.Usize)
    (fits : s.val + 1 ≤ UScalar.max .U64) (inside : r.start.val < s.val + 1 ∧ s.val < r.end.val) :
    run (tree s 0#u32) g r (some item) ds c =
      RustM.ok (.Ok (peakShape g 0 s.val 0 c.val), none, c) := by
  have hr := outside_eq s 0#u32 r (by decide) (by simpa using fits)
  unfold run
  rw [Subtree.reconstruct_digest.eq_def, hr]
  simp [show ¬s.val + 1 ≤ r.start.val by omega, show ¬r.end.val ≤ s.val by omega,
    CoreModels.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch, tree,
    qmdb.Single.Insts.CoreIterTraitsIteratorIteratorElement.next,
    qmdb.Element.Insts.CoreConvertAsRefSliceU8.as_ref, hasher, peakShape]

private theorem children_ok (s : Std.U64) (h : Std.U32) (n : Nat) (hv : h.val = n + 1)
    (bound : h.val ≤ 63) (fits : s.val + 2 ^ h.val ≤ UScalar.max .U64) :
    ∃ (child : Std.U32) (mid : Std.U64),
      (tree s h).children = RustM.ok (tree s child, tree mid child) ∧
      child.val = n ∧ mid.val = s.val + 2 ^ n := by
  obtain ⟨child, sub, cv⟩ := sub_ok h 1#u32 (by scalar_tac)
  have ch : child.val = n := by simp [hv] at cv; omega
  obtain ⟨width, hw, wv⟩ := pow_ok child (by omega)
  rw [hv, Nat.pow_succ] at fits
  obtain ⟨mid, add, mv⟩ := add_ok s width (by rw [wv, ch]; omega)
  exact ⟨child, mid, by simp [tree, Subtree.children, sub, hw, add], ch, by simpa [wv, ch] using mv⟩

private theorem branch {s h child mid g r es ds c l r' es' es'' c' c''}
    (inside : (tree s h).is_outside r = RustM.ok false) (positive : h ≠ 0#u32)
    (kids : (tree s h).children = RustM.ok (tree s child, tree mid child))
    (left : run (tree s child) g r es ds c = RustM.ok (.Ok l, es', c'))
    (right : run (tree mid child) g r es' ds c' = RustM.ok (.Ok r', es'', c'')) :
    run (tree s h) g r es ds c = RustM.ok (.Ok
      (if g && decide (h.val = 8) then .hash (.pair (.atom .bitmap)
        (.hash (.pair (.atom (.word (subtreePosition s.val h.val))) (.pair l r'))))
      else .hash (.pair (.atom (.word (subtreePosition s.val h.val))) (.pair l r'))),
      es'', c'') := by
  unfold run at *
  rw [Subtree.reconstruct_digest.eq_def, inside]
  have nonzero : (tree s h).height ≠ 0#u32 := positive
  simp [nonzero, kids, left, right, core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
  simp [hasher, tree]

/-- For any height and in-range location, the extracted pinned DFS consumes exactly one
operation and one sibling per level. Its symbolic hash program is the plan interpreter's
peakShape, with sibling indices offset past the compressed prefix and suffix peaks. -/
theorem reconstruct_peak (g : Bool) (r : CoreModels.core.ops.range.Range Std.U64)
    (item : Slice Std.U8) (ds : Slice Shape) (base : Nat)
    (refs : ∀ (i : Nat) (hi : i < ds.val.length), ds.val[i] = .atom (.sibling (base + i)))
    (single : r.end.val = r.start.val + 1) (n : Nat) :
    ∀ (h : Std.U32) (s : Std.U64) (c : Std.Usize), h.val = n → n ≤ 63 →
      s.val + 2 ^ n ≤ UScalar.max .U64 →
      s.val ≤ r.start.val → r.start.val < s.val + 2 ^ n →
      c.val + n ≤ ds.length →
      ∃ next : Std.Usize, run (tree s h) g r (some item) ds c = RustM.ok
        (.Ok (peakShape g n s.val (r.start.val - s.val) (base + c.val)), none, next) ∧
        next.val = c.val + n := by
  induction n with
  | zero =>
    intro h s c hv _ fits lower upper _
    obtain rfl : h = 0#u32 := UScalar.eq_of_val_eq hv
    have eq : r.start.val = s.val := by simp at upper; omega
    refine ⟨c, ?_, by omega⟩
    simpa [peakShape] using leaf g s r item ds c (by simpa using fits) (by omega)
  | succ n ih =>
    intro h s c hv bound fits lower upper room
    obtain ⟨k, m, kids, kv, mv⟩ := children_ok s h n hv (by omega) (by simpa [hv] using fits)
    have inside : (tree s h).is_outside r = RustM.ok false := by
      rw [outside_eq _ _ _ (by omega) (by simpa [hv] using fits)]
      simp [hv, show ¬s.val + 2 ^ (n + 1) ≤ r.start.val by omega,
        show ¬r.end.val ≤ s.val by omega]
    have nz : h ≠ 0#u32 := by intro eq; subst h; scalar_tac
    rw [Nat.pow_succ] at upper fits
    by_cases onLeft : r.start.val < m.val
    · obtain ⟨c1, left, cv1⟩ := ih k s c kv (by omega) (by omega) lower (by omega) (by omega)
      obtain ⟨c2, right, cv2⟩ := outside g m k r none ds c1 (by omega) (by omega)
        (by rw [kv]; omega) (Or.inr (by omega))
      rw [refs] at right
      refine ⟨c2, ?_, by omega⟩
      have side : r.start.val - s.val < 2 ^ n := by omega
      have ci : base + c1.val = base + c.val + n := by omega
      simpa only [peakShape, side, ↓reduceIte, ci, hv] using branch inside nz kids left right
    · obtain ⟨c1, left, cv1⟩ := outside g s k r (some item) ds c (by omega) (by omega)
        (by rw [kv]; omega) (Or.inl (by rw [kv]; omega))
      obtain ⟨c2, right, cv2⟩ := ih k m c1 kv (by omega) (by omega)
        (by omega) (by omega) (by omega)
      rw [refs] at left
      refine ⟨c2, ?_, by omega⟩
      have side : ¬r.start.val - s.val < 2 ^ n := by omega
      have loc : r.start.val - (s.val + 2 ^ n) = r.start.val - s.val - 2 ^ n := by omega
      have ci : base + c1.val = base + c.val + 1 := by omega
      simpa only [peakShape, side, ↓reduceIte, ci, loc, mv, hv]
        using branch inside nz kids left right

end
end Qmdb.Mmb.Dfs
