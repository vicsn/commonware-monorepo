module
public import Qmdb.Mmb.Plan

/-! Coverage of the paths constructed by the pinned MMB planner. A grafted chunk's 256 leaves
belong to one peak of height at least eight; all subsequent leaves use a suffix chunk. -/

namespace Qmdb.Mmb
open Active
@[expose] public section

/-- Number of leaves in the remaining k least-significant peaks of a leaf-count successor. -/
def leftWidth (u k : Nat) : Nat := 2 ^ k - 1 + u % 2 ^ k

/-- The next oldest peak accounts for exactly its power-of-two width. -/
theorem width_step (u k : Nat) :
    leftWidth u (k + 1) = 2 ^ peakHeight u k + leftWidth u k := by
  have pos : 0 < 2 ^ k := Nat.two_pow_pos k
  rcases Nat.mod_two_eq_zero_or_one (u / 2 ^ k) with h | h <;>
    simp only [leftWidth, peakHeight, pow_succ, Nat.mod_mul, h, mul_zero, mul_one, add_zero] <;>
  all_goals omega

/-- The initial peak list covers the full MMB. -/
theorem width_all (n : Nat) : leftWidth (n + 1) (n + 1).log2 = n := by
  unfold leftWidth
  have low := Nat.log2_self_le (n := n + 1) (by omega)
  have high := Nat.lt_log2_self (n := n + 1)
  rw [pow_succ] at high
  have pos := Nat.two_pow_pos (n + 1).log2
  rw [Nat.mod_eq_sub_mod low, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem width_small (u k : Nat) (small : peakHeight u k < 8) :
    leftWidth u (k + 1) ≤ 382 := by
  have bound : k ≤ 7 := by unfold peakHeight at small; omega
  by_cases seven : k = 7
  · subst k
    simp only [peakHeight] at small
    change 256 - 1 + u % 256 ≤ 382
    change 7 + u / 128 % 2 < 8 at small
    omega
  · have limit : 2 ^ (k + 1) ≤ 128 := Nat.pow_le_pow_right (by decide) (by omega : k + 1 ≤ 7)
    have rem := Nat.mod_lt u (Nat.two_pow_pos (k + 1))
    unfold leftWidth
    omega

private theorem aligned_skip {cursor height : Nat} (aligned : cursor % 256 = 0)
    (big : 8 ≤ height) : (cursor + 2 ^ height) % 256 = 0 := by
  have hh : height = 8 + (height - 8) := by omega
  conv => lhs; arg 1; arg 2; arg 2; rw [hh]
  simp [pow_add, Nat.add_mod, aligned]

private theorem grafted_height_aux (n k : Nat) : ∀ cursor localLoc i target h off,
    cursor + leftWidth (n + 1) k = n → cursor % 256 = 0 →
    (cursor + localLoc) / 256 < graftedChunks n →
    containing (peakHeights (n + 1) k) i localLoc = some (target, h, off) → 8 ≤ h := by
  induction k with
  | zero => simp [peakHeights, containing]
  | succ k ih =>
    intro cursor localLoc i target h off total aligned grafted found
    have big : 8 ≤ peakHeight (n + 1) k := by
      by_contra! small
      have := width_small _ _ small
      unfold graftedChunks at grafted
      split at grafted <;> omega
    simp only [peakHeights, containing] at found
    split at found
    · cases found
      exact big
    · rename_i skipped
      apply ih (cursor + 2 ^ peakHeight (n + 1) k)
        (localLoc - 2 ^ peakHeight (n + 1) k) (i + 1) target h off
      · rw [width_step] at total
        omega
      · exact aligned_skip aligned big
      · simpa [Nat.add_assoc, Nat.add_sub_of_le (by omega :
          2 ^ peakHeight (n + 1) k ≤ localLoc)] using grafted
      · exact found

/-- Every grafted location passes through its height-eight ancestor. -/
theorem grafted_height {n loc i h off : Nat}
    (grafted : loc / 256 < graftedChunks n)
    (found : containing (heights n) 0 loc = some (i, h, off)) : 8 ≤ h :=
  grafted_height_aux n _ 0 loc 0 i h off (by simp [width_all]) rfl (by simpa using grafted) found

private def Occurs (f : Field) (e : Shape) : Prop := (e.path f).isSome = true

@[simp] private theorem occurs_atom (a f : Field) : Occurs f (.atom a) ↔ a = f := by
  by_cases same : a = f <;> simp [Occurs, Shape.path, same]

@[simp] private theorem occurs_hash (f : Field) (a : Shape) :
    Occurs f (.hash a) ↔ Occurs f a := by
  cases h : a.path f <;> simp [Occurs, Shape.path, h]

@[simp] private theorem occurs_pair (f : Field) (a b : Shape) :
    Occurs f (.pair a b) ↔ Occurs f a ∨ Occurs f b := by
  cases ha : a.path f <;> cases hb : b.path f <;> simp [Occurs, Shape.path, ha, hb, Option.or]

@[simp] private theorem occurs_bag (f : Field) (a b : Shape) :
    Occurs f (bag a b) ↔ Occurs f a ∨ Occurs f b := by simp [bag]

private theorem foldl_bag (f : Field) (xs : List Shape) (x : Shape) :
    Occurs f (xs.foldl bag x) ↔ Occurs f x ∨ ∃ y ∈ xs, Occurs f y := by
  induction xs generalizing x with
  | nil => simp
  | cons a xs ih => simp [List.foldl, ih, or_assoc]

private theorem foldr_bag (f : Field) (xs : List Shape) (x : Shape) :
    Occurs f (xs.foldr bag x) ↔ (∃ y ∈ xs, Occurs f y) ∨ Occurs f x := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.foldr, ih, or_assoc]

private theorem foldFrom_occurs (f : Field) (k : Nat) (first : Shape) (rest : List Shape) :
    Occurs f (foldFrom k first rest) ↔ Occurs f first ∨ ∃ e ∈ rest, Occurs f e := by
  unfold foldFrom
  have parts := List.take_append_drop k rest
  cases hr : (rest.drop k).reverse with
  | nil =>
    have empty := congrArg List.reverse hr
    simp at empty
    simp [foldl_bag, List.take_of_length_le empty]
  | cons l ls =>
    have tailEq := congrArg List.reverse hr
    simp at tailEq
    rw [tailEq] at parts
    conv => rhs; rw [← parts]
    rw [foldr_bag]
    simp [foldl_bag]
    grind

private theorem bagPeaks_occurs (f : Field) (i n : Nat) (first : Shape) (rest : List Shape) :
    Occurs f (bagPeaks i n first rest) ↔ Occurs f first ∨ ∃ e ∈ rest, Occurs f e :=
  foldFrom_occurs f _ first rest

private theorem folded_target (f : Field) (before after : List Shape) (target : Shape) (i n : Nat)
    (has : Occurs f target) :
    Occurs f (match before with
      | [] => bagPeaks i n target after
      | first :: rest => bagPeaks i n first (rest ++ target :: after)) := by
  cases before <;> simp [bagPeaks_occurs, has]
  grind

private theorem peak_item (graft : Bool) (h start off cursor : Nat) :
    Occurs .item (peakShape graft h start off cursor) := by
  induction h generalizing start off cursor with
  | zero => simp [peakShape]
  | succ h ih =>
    simp only [peakShape]
    split <;> split <;> simp [ih]

private theorem peak_bitmap (h start off cursor : Nat) (big : 8 ≤ h) :
    Occurs .bitmap (peakShape true h start off cursor) := by
  induction h generalizing start off cursor with
  | zero => omega
  | succ h ih =>
    simp only [peakShape]
    split <;> split <;> simp_all +decide <;> apply ih <;> omega

private theorem envelope_occurs (leaves inactive loc : Nat) (top : Shape)
    (inside : loc < leaves) (item : Occurs .item top)
    (bitmap : loc / 256 < graftedChunks leaves → Occurs .bitmap top) :
    Occurs .item (envelope leaves inactive loc top) ∧
    Occurs .bitmap (envelope leaves inactive loc top) := by
  have gap : leaves / 256 ≤ graftedChunks leaves + 1 := by unfold graftedChunks; split <;> omega
  have idx : loc / 256 ≤ leaves / 256 := by omega
  have atTail : loc / 256 = leaves / 256 → leaves % 256 ≠ 0 := by omega
  unfold envelope merkleShape
  dsimp only
  by_cases active : loc / 256 < graftedChunks leaves
  · have hb := bitmap active
    by_cases pe : graftedChunks leaves < leaves / 256 <;>
      by_cases tr : leaves % 256 = 0 <;>
      simp only [pe, tr, decide_true, decide_false] <;> split_ifs <;> simp_all
  · have cs : loc / 256 = leaves / 256 ∨
        (loc / 256 = graftedChunks leaves ∧ graftedChunks leaves < leaves / 256) := by omega
    rcases cs with tail | ⟨pend, hasPend⟩
    · have := atTail tail
      by_cases pe : graftedChunks leaves < leaves / 256 <;>
        simp only [pe, decide_true, decide_false] <;> split_ifs <;> simp_all
    · by_cases tr : leaves % 256 = 0 <;> split_ifs <;> simp_all

private theorem assemble_occurs (leaves inactive loc i h off peaks : Nat)
    (inside : loc < leaves) (covered : loc / 256 < graftedChunks leaves → 8 ≤ h) :
    let tree := (assemble leaves inactive loc i h off peaks (loc / 256 < graftedChunks leaves)).tree
    Occurs .item tree ∧ Occurs .bitmap tree := by
  apply envelope_occurs _ _ _ _ inside
  · exact folded_target _ _ _ _ _ _ (peak_item _ _ _ _ _)
  · intro lt
    simp only [lt, decide_true]
    exact folded_target _ _ _ _ _ _ (peak_bitmap _ _ _ _ (covered lt))

/-- Every plan selected for a nonzero chunk contains its item and the bitmap bytes. -/
theorem plan_coverage {leaves inactive loc : Nat} {recipe : Plan}
    (ok : plan leaves inactive loc true = some recipe) :
    (recipe.tree.path .item).isSome ∧ (recipe.tree.path .bitmap).isSome := by
  by_cases inside : loc < leaves
  case neg => simp [plan, inside] at ok
  by_cases limit : leaves ≤ 0x400000000000001e
  case neg => simp [plan, limit] at ok
  by_cases valid : inactive ≤ (heights leaves).length
  case neg => simp [plan, inside, limit, valid] at ok
  cases hc : containing (heights leaves) 0 loc with
  | none => simp [plan, inside, limit, valid, hc] at ok
  | some info =>
    obtain ⟨i, h, off⟩ := info
    simp [plan, inside, limit, valid, hc] at ok
    subst recipe
    exact assemble_occurs leaves inactive loc i h off _ inside (fun g => grafted_height g hc)

end
end Qmdb.Mmb
