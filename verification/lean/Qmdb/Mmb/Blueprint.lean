module
public import Qmdb.Mmb.Plan
public import Qmdb.Mmb.PinnedLayout
public import Commonware.Symbolic.RustM

/-! The pinned backward-fold Blueprint classifies a single range peak, then slices the digest
list. The extraction represents borrowed slices by their endpoints and vectors by their lengths.
These theorems cover the algorithm on arbitrary peak counts, locations and supplied list lengths. -/

namespace Qmdb.Mmb.Blueprint
open Aeneas Aeneas.Std CoreModels Commonware.Symbolic pinned_layout
@[expose] public section

/-- Peak counts in the four classes surrounding the target; the target itself is excluded. -/
structure Groups where
  /-- Older inactive peaks combined in one digest. -/
  fold : Nat
  /-- Older active peaks, each supplied separately. -/
  before : Nat
  /-- Newer inactive peaks, each supplied separately. -/
  after : Nat
  /-- Newer active peaks combined in one digest. -/
  suffix : Nat
  deriving DecidableEq

/-- The ordered classes of a peak relative to the unique target in backward bagging. -/
def groupOf (i target inactive : Nat) : Group :=
  if i < target then
    if i < inactive then .FoldPrefix else .PrefixActivePeaks
  else if target < i then
    if inactive ≤ i then .SuffixPeaks else .AfterPeaks
  else .RangePeaks

/-- The pinned backward-bagging classification loop over the first n peaks. -/
def classify (target inactive : Nat) : Nat → Groups
  | 0 => ⟨0, 0, 0, 0⟩
  | n + 1 =>
    let g := classify target inactive n
    match groupOf n target inactive with
    | .FoldPrefix => {g with fold := g.fold + 1}
    | .PrefixActivePeaks => {g with before := g.before + 1}
    | .AfterPeaks => {g with after := g.after + 1}
    | .SuffixPeaks => {g with suffix := g.suffix + 1}
    | .RangePeaks => g

/-- Interval traversed by the pinned peak iterator at an index of a list of peak heights. -/
def span : List Nat → Nat → Option (Nat × Nat)
  | [], _ => none
  | h :: _, 0 => some (0, 2 ^ h)
  | h :: rest, i + 1 =>
    (span rest i).map fun (start, stop) => (2 ^ h + start, 2 ^ h + stop)

private theorem positive_span {hs : List Nat} {i lo hi : Nat}
    (ok : span hs i = some (lo, hi)) : lo < hi := by
  induction hs generalizing i lo hi with
  | nil => simp [span] at ok
  | cons h hs ih =>
    cases i with
    | zero => cases ok; exact Nat.two_pow_pos h
    | succ i =>
      cases found : span hs i with
      | none => simp [span, found] at ok
      | some bounds =>
        obtain ⟨l, r⟩ := bounds
        simp only [span, found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at ok
        have := ih found
        omega

private theorem index_ge {hs : List Nat} {i loc target h off : Nat}
    (ok : containing hs i loc = some (target, h, off)) : i ≤ target := by
  induction hs generalizing i loc with
  | nil => simp [containing] at ok
  | cons hd hs ih =>
    simp only [containing] at ok
    split at ok
    · cases ok; omega
    · have := ih ok
      omega

/-- For any peak in the traversal, its geometric before/after tests agree with its index relative
to the containing peak. This uses strictly positive widths and includes both interval endpoints. -/
theorem range_class {hs : List Nat} {base loc target height off : Nat}
    (found : containing hs base loc = some (target, height, off))
    {j lo hi : Nat} (bounds : span hs j = some (lo, hi)) :
    (hi ≤ loc ↔ base + j < target) ∧ (loc + 1 ≤ lo ↔ target < base + j) := by
  induction hs generalizing base loc j lo hi with
  | nil => simp [span] at bounds
  | cons h rest ih =>
    simp only [containing] at found
    cases j with
    | zero =>
      cases bounds
      split at found
      · cases found; omega
      · have := index_ge found
        omega
    | succ j =>
      cases hr : span rest j with
      | none => simp [span, hr] at bounds
      | some limits =>
        obtain ⟨l, r⟩ := limits
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (by simpa [span, hr] using bounds :
          some (2 ^ h + l, 2 ^ h + r) = some (lo, hi)))
        split at found
        · cases found
          have := positive_span hr
          omega
        · obtain ⟨older, newer⟩ := ih found hr
          omega

/-- The extracted decision for each peak in a singleton range gives the class counted
by the proof plan. Vector pushes are projected to the identity of their destination. -/
theorem rust_classifies {hs : List Nat} {target h off : Nat} (loc stop : Std.U64)
    (endLoc : stop.val = loc.val + 1) (start endPeak : Std.U64) (i inactive : Std.Usize)
    (found : containing hs 0 loc.val = some (target, h, off))
    (bounds : span hs i.val = some (start.val, endPeak.val)) :
    classify_peak start endPeak ⟨loc, stop⟩ i inactive =
      RustM.ok (groupOf i.val target inactive.val) := by
  obtain ⟨older, newer⟩ := range_class found bounds
  simp only [Nat.zero_add] at older newer
  simp [classify_peak, groupOf, endLoc, older, newer]
  split_ifs <;> rfl
/-- Prefix, suffix and individual counts agree with the closed form for all peak lists. -/
theorem classify_eq (i inactive n : Nat) :
    classify i inactive n =
      ⟨min (min i inactive) n, min i n - inactive, min n inactive - (i + 1),
        n - max (i + 1) inactive⟩ := by
  induction n with
  | zero => simp [classify]
  | succ n ih =>
    simp only [classify, groupOf, ih]
    split_ifs <;> dsimp only <;> congr 1 <;> omega

/-- Optional offset of a compressed accumulator. -/
def optionalOffset : core.option.Option Std.Usize → Option Nat
  | .Some v => some v.val
  | .None => none

/-- Project the presence of a peak group into the usize used by the extracted splitter. -/
def oneIf (n : Std.Usize) : Std.Usize := if n = 0#usize then 0#usize else 1#usize

private theorem flag_ok (n : Std.Usize) :
    core.Usize.Insts.CoreConvertFromBool.from (n != 0#usize) = RustM.ok (oneIf n) := by
  by_cases z : n = 0#usize <;> simp [z, oneIf, core.Usize.Insts.CoreConvertFromBool.from]

private theorem flag_le (n : Std.Usize) : (oneIf n).val ≤ 1 := by
  unfold oneIf; split <;> decide

/-- All five slices and offsets returned by the pinned splitter at the exact required length. -/
def Offsets (bp : pinned_layout.Blueprint) (v : ProofDigestLayout) : Prop :=
  let fold := (oneIf bp.fold_prefix).val
  let before := fold + bp.prefix_active_peaks.val
  let after := before + bp.after_peaks.val
  optionalOffset v.fold_prefix = (if bp.fold_prefix = 0#usize then none else some 0) ∧
    (v.prefix_active_peaks.start.val, v.prefix_active_peaks.«end».val) = (fold, before) ∧
    (v.after_peaks.start.val, v.after_peaks.«end».val) = (before, after) ∧
    optionalOffset v.suffix_acc = (if bp.suffix_peaks = 0#usize then none else some after) ∧
    v.siblings.start.val = after + (oneIf bp.suffix_peaks).val

/-- The extracted Rust splitter rejects short/long lists and selects exactly the stated offsets.
The blueprint construction puts individual peak positions before the DFS sibling positions. -/
theorem split_spec (bp : pinned_layout.Blueprint) (len : Std.Usize)
    (fetch : bp.prefix_active_peaks.val + bp.after_peaks.val ≤ bp.fetch_nodes.val)
    (fits : bp.fetch_nodes.val + 2 ≤ UScalar.max .Usize) :
    let required := (oneIf bp.fold_prefix).val + bp.fetch_nodes.val + (oneIf bp.suffix_peaks).val
    ∃ res, bp.split_proof_digests len = RustM.ok res ∧
      match res with
      | .Err .MissingDigests => len.val < required
      | .Err .ExtraDigests => len.val > required
      | .Ok v => len.val = required ∧ Offsets bp v := by
  dsimp only
  have f := flag_le bp.fold_prefix
  have s := flag_le bp.suffix_peaks
  obtain ⟨m, hm, mv⟩ := add_ok (oneIf bp.fold_prefix) bp.fetch_nodes (by omega)
  obtain ⟨required, hr, rv⟩ := add_ok m (oneIf bp.suffix_peaks) (by omega)
  obtain ⟨before, hb, bv⟩ := add_ok (oneIf bp.fold_prefix) bp.prefix_active_peaks (by omega)
  obtain ⟨after, ha, av⟩ := add_ok before bp.after_peaks (by omega)
  obtain ⟨endS, he, ev⟩ := add_ok after (oneIf bp.suffix_peaks) (by omega)
  by_cases short : len.val < required.val
  · refine ⟨.Err .MissingDigests, ?_, ?_⟩
    · simp [pinned_layout.Blueprint.split_proof_digests, flag_ok, hm, hr, short]
    · omega
  by_cases long : required.val < len.val
  · refine ⟨.Err .ExtraDigests, ?_, ?_⟩
    · simp [pinned_layout.Blueprint.split_proof_digests, flag_ok, hm, hr, short, long]
    · omega
  let foldOff : core.option.Option Std.Usize :=
    if bp.fold_prefix.val = 0 then .None else .Some 0#usize
  let suffixOff : core.option.Option Std.Usize :=
    if bp.suffix_peaks.val = 0 then .None else .Some after
  refine ⟨.Ok ⟨foldOff, ⟨oneIf bp.fold_prefix, before⟩, ⟨before, after⟩,
    suffixOff, ⟨endS⟩⟩, ?_, (by omega), ?_⟩
  · simp [pinned_layout.Blueprint.split_proof_digests, flag_ok, hm, hr, hb, ha, he, short, long]
    split_ifs <;> simp_all [foldOff, suffixOff]
  · by_cases fo : bp.fold_prefix.val = 0 <;> by_cases su : bp.suffix_peaks.val = 0 <;>
      simp [Offsets, optionalOffset, foldOff, suffixOff, fo, su, bv, av, ev]

/-- Identification of Rust vector lengths with the single-range-peak classification.
The positions fetched individually include the h DFS siblings. -/
def Describes (bp : pinned_layout.Blueprint) (g : Groups) (h : Nat) : Prop :=
  bp.fold_prefix.val = g.fold ∧ bp.prefix_active_peaks.val = g.before ∧
    bp.after_peaks.val = g.after ∧ bp.suffix_peaks.val = g.suffix ∧
    bp.fetch_nodes.val = g.before + g.after + h

private theorem flag_val (x : Std.Usize) : (oneIf x).val = if x.val = 0 then 0 else 1 := by
  unfold oneIf
  by_cases e : x = 0#usize
  · subst x; rfl
  · have ne : x.val ≠ 0 := fun h => e (UScalar.eq_of_val_eq h)
    simp [e, ne]

/-- The pinned splitter and the single-operation plan agree on digest count, placement of the
reconstructed target, and start of its h DFS siblings, for every supplied list length. -/
theorem split_plan (bp : pinned_layout.Blueprint) (len : Std.Usize)
    {leaves inactive loc i h off peaks : Nat} {graft : Bool}
    (inRange : i < peaks) (boundary : inactive ≤ peaks)
    (repr : Describes bp (classify i inactive peaks) h)
    (fits : bp.fetch_nodes.val + 2 ≤ UScalar.max .Usize) :
    let count := (assemble leaves inactive loc i h off peaks graft).count
    ∃ res, bp.split_proof_digests len = RustM.ok res ∧
      match res with
      | .Err .MissingDigests => len.val < count
      | .Err .ExtraDigests => len.val > count
      | .Ok v => len.val = count ∧ Offsets bp v ∧
          v.prefix_active_peaks.«end».val =
            (if min i inactive = 0 then 0 else 1) + (i - inactive) ∧
          v.siblings.start.val + h = count := by
  dsimp only
  rw [classify_eq] at repr
  obtain ⟨f, b, a, s, fetch⟩ := repr
  simp only [Nat.min_eq_left (by omega : i ≤ peaks),
    Nat.min_eq_left (by omega : min i inactive ≤ peaks),
    Nat.min_eq_right boundary] at f b a s fetch
  have size :
      (oneIf bp.fold_prefix).val + bp.fetch_nodes.val + (oneIf bp.suffix_peaks).val =
        (assemble leaves inactive loc i h off peaks graft).count := by
    simp only [assemble, flag_val, f, fetch, s]
    split_ifs <;> omega
  obtain ⟨res, run, verdict⟩ := split_spec bp len (by omega) fits
  refine ⟨res, run, ?_⟩
  cases res with
  | Err err => cases err <;> simpa only [← size] using verdict
  | Ok v =>
    obtain ⟨eq, offsets⟩ := verdict
    have saved := offsets
    obtain ⟨_, prefixRange, _, _, siblingStart⟩ := offsets
    have prefixEnd := congrArg Prod.snd prefixRange
    dsimp only at prefixEnd
    refine ⟨eq.trans size, saved, ?_, ?_⟩
    · simpa [flag_val, f, b] using prefixEnd
    · rw [← size, siblingStart]
      omega

end
end Qmdb.Mmb.Blueprint
