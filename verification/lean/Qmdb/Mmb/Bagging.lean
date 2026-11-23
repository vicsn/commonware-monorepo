module
import all Aeneas.Std.Scalar.SaturatingOps
public import Qmdb.Mmb.Plan
public import Qmdb.Mmb.PinnedBag
public import Commonware.Symbolic.RustM

/-! The pinned backward bagger specialized to a finite iterator of opaque peak digests. -/

namespace Qmdb.Mmb.Bagging
open Aeneas Aeneas.Std CoreModels Commonware.Symbolic pinned_bag
@[expose] public section

/-- Model the pinned hash calls by their ordered symbolic preimages. -/
def hashing : Hash Unit Shape where
  coremarkerCopyInst := ⟨⟨RustM.ok, fun _ x => RustM.ok x⟩⟩
  fold _ a b := RustM.ok (bag a b)
  root _ leaves n peak := RustM.ok (match n with
    | .None => .hash (.pair (.atom (.word leaves.val)) peak)
    | .Some count => .hash (.pair (.atom (.word leaves.val))
        (.pair (.atom (.word count.val)) peak)))
  empty _ n := RustM.ok (.hash (.atom (.word n.val)))

/-- A forward slice iterator, or the reverse iterator over the accumulated head and suffix. -/
def cursor : Cursor (List Shape) Shape where
  next
    | [] => RustM.ok (.None, [])
    | h :: t => RustM.ok (.Some h, t)
  reversed_with_head xs x := RustM.ok (x :: xs).reverse

private theorem sat_val (x y : Std.Usize) :
    (UScalar.saturating_sub x y).val = x.val - y.val := by
  rw [← UScalar.bv_toNat (UScalar.saturating_sub x y)]
  simp only [UScalar.saturating_sub]
  simp only [Nat.zero_max, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.bv.isLt)

/-- The inactive prefix loop consumes exactly count operands and rejects exhaustion. -/
theorem prefix_eq (xs : List Shape) (count : Std.Usize) (acc : Shape) :
    pinned_bag.«prefix» hashing cursor () xs count acc = RustM.ok
      (if count.val ≤ xs.length then
        .Some ((xs.take count.val).foldl bag acc, xs.drop count.val) else .None) := by
  induction xs generalizing acc count with
  | nil =>
    rw [pinned_bag.«prefix».eq_def]
    by_cases z : count.val = 0 <;>
      simp [cursor, z, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
  | cons x xs ih =>
    rw [pinned_bag.«prefix».eq_def]
    by_cases z : count.val = 0
    · simp [z]
    · obtain ⟨pred, sub, pv⟩ := sub_ok count 1#usize (by change 1 ≤ count.val; omega)
      have succ : count.val = pred.val + 1 := by change pred.val = count.val - 1 at pv; omega
      simp [cursor, hashing, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        sub, succ]
      simpa [cursor, hashing] using ih pred (bag acc x)

/-- Reverse iteration puts each older prefix on the left of the accumulator. -/
theorem backward_eq (left : List Shape) (acc : Shape) :
    pinned_bag.backward hashing cursor () left acc =
      RustM.ok (left.foldl (fun a p => bag p a) acc) := by
  induction left generalizing acc with
  | nil => rw [pinned_bag.backward.eq_def]; simp [cursor]
  | cons x xs ih => rw [pinned_bag.backward.eq_def]; simpa [cursor, hashing] using ih (bag x acc)

/-- The adjusted inactive count for one compressed prefix. -/
theorem adjusted (pre inactive : Std.Usize) (fits : inactive.val < UScalar.max .Usize) :
    ∃ kept, inactive_peaks_after_prefix_fold pre inactive = RustM.ok kept ∧
      kept.val = if pre.val = 0 then inactive.val else inactive.val - pre.val + 1 := by
  by_cases noPrefix : pre.val = 0
  · exact ⟨inactive, by simp [inactive_peaks_after_prefix_fold, noPrefix], by simp [noPrefix]⟩
  · obtain ⟨k, add, kv⟩ := add_ok (UScalar.saturating_sub inactive pre) 1#usize
      (by rw [sat_val]; change _ + 1 ≤ _; omega)
    refine ⟨k, ?_, ?_⟩
    · simp [inactive_peaks_after_prefix_fold, noPrefix, CoreModels.core.num.Usize.saturating_sub,
        rust_primitives.arithmetic.saturating_sub_usize, add]
    · simpa [sat_val, noPrefix] using kv

/-- Empty input is valid only with both inactive counts zero. -/
theorem empty_eq (leaves : Std.U64) (kept inactive : Std.Usize) :
    pinned_bag.root hashing cursor () leaves kept inactive [] = RustM.ok
      (if kept.val = 0 ∧ inactive.val = 0 then .Some (.hash (.atom (.word leaves.val)))
        else .None) := by
  simp [pinned_bag.root, cursor, hashing]
  split_ifs <;> simp_all

private theorem reversed_loop (first : Shape) (rest : List Shape) :
    (match (first :: rest).reverse with
      | [] => none
      | last :: xs => some (xs.foldl (fun a p => bag p a) last)) =
    some (match rest.reverse with
      | [] => first
      | last :: rev => (first :: rev.reverse).foldr bag last) := by
  simp only [List.reverse_cons]
  cases h : rest.reverse <;> simp [List.foldl_append]

/-- The nonempty backward bagger rejects excess inactive operands. Otherwise its Merkle
preimage is exactly the plan's forward prefix and backward suffix under the committed counts. -/
theorem nonempty_eq (leaves : Std.U64) (kept inactive : Std.Usize) (first : Shape)
    (rest : List Shape) :
    pinned_bag.root hashing cursor () leaves kept inactive (first :: rest) = RustM.ok
      (if kept.val - 1 ≤ rest.length then
        .Some (merkleShape leaves.val inactive.val (foldFrom (kept.val - 1) first rest))
       else .None) := by
  let pred := UScalar.saturating_sub kept 1#usize
  have pv : pred.val = kept.val - 1 := sat_val _ _
  have sat : CoreModels.core.num.Usize.saturating_sub kept 1#usize = RustM.ok pred := by
    simp [CoreModels.core.num.Usize.saturating_sub, rust_primitives.arithmetic.saturating_sub_usize,
      pred]
  have init : cursor.next (first :: rest) = RustM.ok (.Some first, rest) := rfl
  simp [pinned_bag.root, init, sat, prefix_eq, pv]
  by_cases fits : kept.val ≤ rest.length + 1
  case neg =>
    simp [fits, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
  simp [fits, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch]
  let a := (rest.take (kept.val - 1)).foldl bag first
  let xs := rest.drop (kept.val - 1)
  have reverseOK : cursor.reversed_with_head xs a = RustM.ok (a :: xs).reverse := rfl
  rw [reverseOK]
  have foldEq := reversed_loop a xs
  cases hr : (a :: xs).reverse with
  | nil => simp [hr] at foldEq
  | cons last prior =>
    simp only [hr, Option.some.injEq] at foldEq
    have next : cursor.next (last :: prior) = RustM.ok (.Some last, prior) := rfl
    simp [next, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      backward_eq, foldEq]
    by_cases zero : inactive = 0#usize
    · subst inactive
      cases hs : (rest.drop (kept.val - 1)).reverse <;>
        simp [hashing, merkleShape, foldFrom, a, hs]
    · have nz : inactive.val ≠ 0 := fun h => zero (UScalar.eq_of_val_eq h)
      cases hs : (rest.drop (kept.val - 1)).reverse <;>
        simp [hashing, merkleShape, foldFrom, zero, nz, a, lift, hs]

/-- The projected pinned counter adjustment and backward bagger produce the exact root in the
single-peak plan, including both header formats and every compressed prefix and suffix size. -/
theorem compressed_eq (leaves : Std.U64) (inactive pre : Std.Usize) (i peaks : Nat)
    (bounds : inactive.val ≤ peaks) (inside : i < peaks)
    (fits : inactive.val < UScalar.max .Usize) (prefixSize : pre.val = min i inactive.val)
    (first : Shape) (rest : List Shape)
    (count : rest.length =
      ((if min i inactive.val = 0 then 0 else 1) + (i - inactive.val)) +
      ((inactive.val - (i + 1)) + (if max (i + 1) inactive.val < peaks then 1 else 0))) :
    ∃ kept, inactive_peaks_after_prefix_fold pre inactive = RustM.ok kept ∧
      pinned_bag.root hashing cursor () leaves kept inactive (first :: rest) = RustM.ok
        (.Some (merkleShape leaves.val inactive.val (bagPeaks i inactive.val first rest))) := by
  obtain ⟨k, run, kv⟩ := adjusted pre inactive fits
  rw [prefixSize] at kv
  refine ⟨k, run, ?_⟩
  have room : k.val - 1 ≤ rest.length := by
    rw [kv, count]
    split_ifs <;> omega
  rw [nonempty_eq, ite_eq_left room, kv]
  rfl

end
end Qmdb.Mmb.Bagging
