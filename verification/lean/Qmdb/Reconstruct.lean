module
import all Aeneas.Std.Scalar.SaturatingOps
public import Qmdb.Assumptions
public import Commonware.Symbolic.RustM

/-! The extracted production range-proof reconstruction on DyLean terms, for a proof of one
location. `reconstruct` lists the peaks of the structure around the one containing the location,
rebuilds that peak with the traversal and bags the list into a root. Checked by Lean; the peaks
of a family and the traversal of the containing peak are hypotheses that each target discharges
for its own geometry and nodes. -/

namespace Qmdb.Reconstruct
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-! ## Hash inputs -/

/-- The big-endian bytes of a 64-bit integer. -/
def be (x : Std.U64) : Slice Std.U8 :=
  (Aeneas.Std.core.num.U64.to_be_bytes x).to_slice

/-- The digest of a peak folded into an accumulator. -/
def foldTerm (acc peak : Bytes) : Bytes :=
  Hash.hash (Concat.concat acc peak)

/-- The root over a bag of peaks, committing `domain`, the leaf count and a nonzero inactive
count. -/
def rootTerm (domain : Aeneas.Std.Array Std.U8 2#usize) (leaves inactive : Std.U64)
    (bag : Bytes) : Bytes :=
  if inactive = 0#u64 then
    Hash.hash (chain [.Bytes domain.to_slice, .Bytes (be leaves), .Digest bag])
  else
    Hash.hash (chain [.Bytes domain.to_slice, .Bytes (be leaves), .Bytes (be inactive),
      .Digest bag])

theorem to_be_bytes_ok (x : Std.U64) :
    CoreModels.core.num.U64.to_be_bytes x = RustM.ok (Aeneas.Std.core.num.U64.to_be_bytes x) := by
  simp [CoreModels.core.num.U64.to_be_bytes, rust_primitives.arithmetic.to_be_bytes_u64]

theorem fold_eq (acc peak : Bytes) :
    terms.fold dyTerms () acc peak = RustM.ok (foldTerm acc peak) := by
  simp [terms.fold, core.array.Array.as_slice, rust_primitives.slice.array_as_slice, dyTerms,
    foldTerm, chain, part]

theorem root_eq (domain : Aeneas.Std.Array Std.U8 2#usize) (leaves inactive : Std.U64)
    (bag : Bytes) :
    terms.root dyTerms () domain leaves inactive bag =
      RustM.ok (rootTerm domain leaves inactive bag) := by
  unfold terms.root rootTerm
  split <;> simp [to_be_bytes_ok, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, dyTerms, be]

/-! ## Bagging -/

/-- Fold the first `k` of `rest` into `first` oldest first; then fold the remaining peaks in the
same order, or, backward, from the newest into one bag that is folded into the accumulator. -/
def bagWith {α : Type} (f : α → α → α) (backward : Bool) (k : Nat) (first : α)
    (rest : List α) : α :=
  let acc := (rest.take k).foldl f first
  if backward then
    match (rest.drop k).reverse with
    | [] => acc
    | last :: rev => f acc (rev.foldl (fun bag peak => f peak bag) last)
  else (rest.drop k).foldl f acc

/-- Backward bagging of a nonempty remainder: its peaks but the newest fold over the newest,
and the result folds into the accumulator. -/
theorem bagWith_backward {α : Type} (f : α → α → α) (k : Nat) (first : α) (rest : List α)
    (h : rest.drop k ≠ []) :
    bagWith f true k first rest =
      f ((rest.take k).foldl f first) ((rest.drop k).dropLast.foldr f ((rest.drop k).getLast h)) := by
  unfold bagWith
  simp only [↓reduceIte]
  conv => lhs; rw [← List.dropLast_append_getLast h]
  simp [List.foldl_reverse]

/-- Backward bagging with nothing left after the forward fold. -/
theorem bagWith_empty {α : Type} (f : α → α → α) (k : Nat) (first : α) (rest : List α)
    (h : rest.drop k = []) : bagWith f true k first rest = (rest.take k).foldl f first := by
  unfold bagWith
  simp [h]

/-- Forward bagging folds the remainder into the accumulator. -/
theorem bagWith_forward {α : Type} (f : α → α → α) (k : Nat) (first : α) (rest : List α) :
    bagWith f false k first rest = (rest.drop k).foldl f ((rest.take k).foldl f first) := by
  simp [bagWith]

/-- The cursor over a slice of digests. -/
abbrev ends := reconstruct.Ends.Insts.Commonware_symbolicTermsCursor
  dyTerms.coremarkerCopyInst

/-- The cursor's read from the oldest end. -/
abbrev endsNext := reconstruct.Ends.Insts.Commonware_symbolicTermsCursor.next (D := Bytes)
  dyTerms.coremarkerCopyInst

/-- The cursor's read from the newest end. -/
abbrev endsNextBack := reconstruct.Ends.Insts.Commonware_symbolicTermsCursor.next_back
  (D := Bytes) dyTerms.coremarkerCopyInst

theorem index_ok {α} (s : Slice α) (i : Std.Usize) (bound : i.val < s.val.length) :
    Slice.index_usize s i = RustM.ok (s.val[i.val]'bound) := by
  obtain ⟨x, hx, _, rfl⟩ := ok_of_partialSpec (Slice.index_usize_spec s i)
    (by intro e; cases e <;> simp; omega) (by simp)
  exact hx

theorem next_some (e : reconstruct.Ends Bytes) (lt : e.front.val < e.back.val)
    (inside : e.back.val ≤ e.digests.val.length) :
    ∃ f : Std.Usize, endsNext e = RustM.ok (.Some (e.digests.val[e.front.val]'(by omega)),
      { e with front := f }) ∧ f.val = e.front.val + 1 := by
  obtain ⟨f, hf, fv⟩ := add_ok e.front 1#usize (by scalar_tac)
  refine ⟨f, ?_, by simpa using fv⟩
  have lt' : e.front < e.back := lt
  simp [reconstruct.Ends.Insts.Commonware_symbolicTermsCursor.next, lt',
    index_ok e.digests e.front (by omega), hf]

theorem next_none (e : reconstruct.Ends Bytes) (ge : ¬ e.front.val < e.back.val) :
    endsNext e = RustM.ok (.None, e) := by
  have ge' : ¬ e.front < e.back := ge
  simp [reconstruct.Ends.Insts.Commonware_symbolicTermsCursor.next, ge']

theorem next_back_some (e : reconstruct.Ends Bytes) (lt : e.front.val < e.back.val)
    (inside : e.back.val ≤ e.digests.val.length) :
    ∃ b : Std.Usize, endsNextBack e =
      RustM.ok (.Some (e.digests.val[e.back.val - 1]'(by omega)),
      { e with back := b }) ∧ b.val = e.back.val - 1 := by
  obtain ⟨b, hb, bv⟩ := sub_ok e.back 1#usize (by scalar_tac)
  refine ⟨b, ?_, by simpa using bv⟩
  have lt' : e.front < e.back := lt
  have bv' : b.val = e.back.val - 1 := by simpa using bv
  simp [reconstruct.Ends.Insts.Commonware_symbolicTermsCursor.next_back, lt', hb,
    index_ok e.digests b (by omega), bv']

theorem next_back_none (e : reconstruct.Ends Bytes) (ge : ¬ e.front.val < e.back.val) :
    endsNextBack e = RustM.ok (.None, e) := by
  have ge' : ¬ e.front < e.back := ge
  simp [reconstruct.Ends.Insts.Commonware_symbolicTermsCursor.next_back, ge']

/-- The prefix fold reads `to_fold - 1` more peaks into the accumulator, or fails if the cursor
runs out. -/
theorem fold_prefix_eq (e : reconstruct.Ends Bytes) (acc : Bytes) (to_fold folded : Std.Usize)
    (inside : e.back.val ≤ e.digests.val.length) (pos : 1 ≤ folded.val) :
    ∃ e', terms.fold_prefix_loop dyTerms ends () to_fold e acc folded = RustM.ok
      (if to_fold.val - folded.val ≤ e.back.val - e.front.val then
        .Some (((e.digests.val.drop e.front.val).take (to_fold.val - folded.val)).foldl
          foldTerm acc)
      else .None, e') ∧
      e'.digests = e.digests ∧ e'.back = e.back ∧
      (to_fold.val - folded.val ≤ e.back.val - e.front.val →
        e'.front.val = e.front.val + (to_fold.val - folded.val)) := by
  generalize hn : to_fold.val - folded.val = n
  induction n generalizing e acc folded with
  | zero =>
    refine ⟨e, ?_, rfl, rfl, fun _ => by simp⟩
    rw [terms.fold_prefix_loop, loop.eq_def]
    have done : folded ≥ to_fold := by scalar_tac
    simp [terms.fold_prefix_loop.body, done]
  | succ n ih =>
    have notDone : ¬ folded ≥ to_fold := by scalar_tac
    by_cases room : e.front.val < e.back.val
    · obtain ⟨f, hf, fv⟩ := next_some e room inside
      obtain ⟨folded', hfolded, foldedv⟩ := add_ok folded 1#usize (by scalar_tac)
      have step : terms.fold_prefix_loop.body dyTerms ends () to_fold e acc folded =
          RustM.ok (.cont ({ e with front := f },
            foldTerm acc (e.digests.val[e.front.val]'(by omega)), folded')) := by
        simp [terms.fold_prefix_loop.body, notDone, hf, fold_eq, hfolded]
      obtain ⟨e', run, hd, hb, hf'⟩ := ih { e with front := f }
        (foldTerm acc (e.digests.val[e.front.val]'(by omega))) folded' (by simpa using inside)
        (by simp at foldedv; omega) (by simp at foldedv; omega)
      refine ⟨e', ?_, hd, hb, fun fits => ?_⟩
      · unfold terms.fold_prefix_loop
        rw [loop_cont _ _ _ step]
        unfold terms.fold_prefix_loop at run
        rw [run]
        have fv' : f.val = e.front.val + 1 := by simpa using fv
        have drop : e.digests.val.drop e.front.val =
            (e.digests.val[e.front.val]'(by omega)) :: e.digests.val.drop (e.front.val + 1) :=
          List.drop_eq_getElem_cons (by omega)
        dsimp only
        rw [fv', drop]
        by_cases fit : n ≤ e.back.val - (e.front.val + 1)
        · have fit' : n + 1 ≤ e.back.val - e.front.val := by omega
          simp only [fit, fit', ite_true, List.take_succ_cons, List.foldl_cons]
        · have fit' : ¬ n + 1 ≤ e.back.val - e.front.val := by omega
          simp only [fit, fit', ite_false]
      · have := hf' (by simp [fv]; omega)
        simp [fv] at this
        omega
    · refine ⟨e, ?_, rfl, rfl, fun fits => by omega⟩
      have step : terms.fold_prefix_loop.body dyTerms ends () to_fold e acc folded =
          RustM.ok (.done (.None, e)) := by
        simp [terms.fold_prefix_loop.body, notDone, next_none e room]
      unfold terms.fold_prefix_loop
      rw [loop_done _ _ _ step]
      simp
      omega

/-- The backward loop folds the unread peaks from the newest into the bag. -/
theorem backward_eq (e : reconstruct.Ends Bytes) (bag : Bytes)
    (inside : e.back.val ≤ e.digests.val.length) (order : e.front.val ≤ e.back.val) :
    ∃ e', terms.bagged_root_loop0 dyTerms ends e () bag = RustM.ok (e',
      ((e.digests.val.drop e.front.val).take (e.back.val - e.front.val)).foldr foldTerm bag) := by
  generalize hn : e.back.val - e.front.val = n
  induction n generalizing e bag with
  | zero =>
    refine ⟨e, ?_⟩
    have empty : ¬ e.front.val < e.back.val := by omega
    have step : terms.bagged_root_loop0.body dyTerms ends () e bag =
        RustM.ok (.done (e, bag)) := by
      simp [terms.bagged_root_loop0.body, next_back_none e empty]
    unfold terms.bagged_root_loop0
    rw [loop_done _ _ _ step]
    simp
  | succ n ih =>
    have room : e.front.val < e.back.val := by omega
    obtain ⟨b, hb, bv⟩ := next_back_some e room inside
    have step : terms.bagged_root_loop0.body dyTerms ends () e bag =
        RustM.ok (.cont ({ e with back := b },
          foldTerm (e.digests.val[e.back.val - 1]'(by omega)) bag)) := by
      simp [terms.bagged_root_loop0.body, hb, fold_eq]
    obtain ⟨e', run⟩ := ih { e with back := b }
      (foldTerm (e.digests.val[e.back.val - 1]'(by omega)) bag)
      (by simp [bv]; omega) (by simp [bv]; omega) (by simp [bv]; omega)
    refine ⟨e', ?_⟩
    unfold terms.bagged_root_loop0
    rw [loop_cont _ _ _ step]
    unfold terms.bagged_root_loop0 at run
    rw [run]
    have split : (e.digests.val.drop e.front.val).take (n + 1) =
        (e.digests.val.drop e.front.val).take n ++ [e.digests.val[e.back.val - 1]'(by omega)] := by
      rw [List.take_add_one]
      congr 1
      rw [List.getElem?_drop]
      have : e.front.val + n = e.back.val - 1 := by omega
      rw [this, List.getElem?_eq_getElem (by omega)]
      rfl
    rw [split, List.foldr_append]
    rfl

/-- The forward loop folds the unread peaks into the accumulator, oldest first. -/
theorem forward_eq (e : reconstruct.Ends Bytes) (acc : Bytes)
    (inside : e.back.val ≤ e.digests.val.length) (order : e.front.val ≤ e.back.val) :
    ∃ e', terms.bagged_root_loop1 dyTerms ends e () acc = RustM.ok (e',
      ((e.digests.val.drop e.front.val).take (e.back.val - e.front.val)).foldl foldTerm acc) := by
  generalize hn : e.back.val - e.front.val = n
  induction n generalizing e acc with
  | zero =>
    refine ⟨e, ?_⟩
    have empty : ¬ e.front.val < e.back.val := by omega
    have step : terms.bagged_root_loop1.body dyTerms ends () e acc =
        RustM.ok (.done (e, acc)) := by
      simp [terms.bagged_root_loop1.body, next_none e empty]
    unfold terms.bagged_root_loop1
    rw [loop_done _ _ _ step]
    simp
  | succ n ih =>
    have room : e.front.val < e.back.val := by omega
    obtain ⟨f, hf, fv⟩ := next_some e room inside
    have step : terms.bagged_root_loop1.body dyTerms ends () e acc =
        RustM.ok (.cont ({ e with front := f },
          foldTerm acc (e.digests.val[e.front.val]'(by omega)))) := by
      simp [terms.bagged_root_loop1.body, hf, fold_eq]
    obtain ⟨e', run⟩ := ih { e with front := f }
      (foldTerm acc (e.digests.val[e.front.val]'(by omega))) (by simpa using inside)
      (by simp [fv]; omega) (by simp [fv]; omega)
    refine ⟨e', ?_⟩
    unfold terms.bagged_root_loop1
    rw [loop_cont _ _ _ step]
    unfold terms.bagged_root_loop1 at run
    rw [run]
    have fv' : f.val = e.front.val + 1 := by simpa using fv
    have drop : e.digests.val.drop e.front.val =
        (e.digests.val[e.front.val]'(by omega)) :: e.digests.val.drop (e.front.val + 1) :=
      List.drop_eq_getElem_cons (by omega)
    dsimp only
    rw [fv', drop, List.take_succ_cons, List.foldl_cons]

/-- The bag of a nonempty list of peaks, folding `to_fold` of them forward first. The root exists
exactly when that many peaks are listed. -/
theorem bagged_root_eq (domain : Aeneas.Std.Array Std.U8 2#usize) (backward : Bool)
    (leaves : Std.U64) (to_fold : Std.Usize) (committed : Std.U64) (L : Slice Bytes)
    (first : Bytes) (rest : List Bytes) (listed : L.val = first :: rest) :
    ∃ e', terms.bagged_root dyTerms ends () domain backward leaves to_fold committed
      ⟨L, 0#usize, Slice.len L⟩ = RustM.ok
      (if to_fold.val ≤ L.val.length then
        .Some (rootTerm domain leaves committed
          (bagWith foldTerm backward (to_fold.val - 1) first rest))
      else .None, e') := by
  have lenv : (Slice.len L).val = rest.length + 1 := by simp [listed]
  have room : (0#usize : Std.Usize).val < (Slice.len L).val := by simp [lenv]
  obtain ⟨one, hone, onev⟩ := next_some ⟨L, 0#usize, Slice.len L⟩ room (by simp)
  have firstEq : L.val[0]'(by simp [listed]) = first := by
    simp [listed]
  obtain ⟨e₁, pre, hd, hb, hf⟩ := fold_prefix_eq ⟨L, one, Slice.len L⟩ first to_fold 1#usize
    (by simp) (by simp)
  have onev' : one.val = 1 := by simpa using onev
  simp only at hd hb hf
  have hb' : e₁.back.val = rest.length + 1 := by rw [hb, lenv]
  have hlen : L.val.length = rest.length + 1 := by simp [listed]
  have drop1 : L.val.drop 1 = rest := by simp [listed]
  unfold terms.bagged_root
  simp [hone, firstEq, terms.fold_prefix, pre]
  by_cases fits : to_fold.val ≤ L.val.length
  · have fits' : to_fold.val ≤ L.val.length - 1 + 1 := by omega
    have front : e₁.front.val = to_fold.val - 1 + 1 := by
      have := hf (by simp [onev', lenv]; omega)
      simp [onev'] at this
      omega
    have inside : e₁.back.val ≤ e₁.digests.val.length := by rw [hd, hb']; simp [listed]
    have order : e₁.front.val ≤ e₁.back.val := by rw [front, hb']; omega
    have remEq : e₁.digests.val.drop e₁.front.val = rest.drop (to_fold.val - 1) := by
      rw [hd, front, ← drop1, List.drop_drop]
      congr 1
      omega
    have remLen : (rest.drop (to_fold.val - 1)).length = e₁.back.val - e₁.front.val := by
      rw [← remEq]; simp [hd, hb', hlen]
    cases backward with
    | true =>
      by_cases more : e₁.front.val < e₁.back.val
      · obtain ⟨b, hbk, bv⟩ := next_back_some e₁ more inside
        obtain ⟨e₂, run⟩ := backward_eq { e₁ with back := b }
          (e₁.digests.val[e₁.back.val - 1]'(by omega)) (by simp [bv]; omega)
          (by simp [bv]; omega)
        have nonempty : rest.drop (to_fold.val - 1) ≠ [] := by
          intro empty; rw [empty] at remLen; simp at remLen; omega
        have lastEq : e₁.digests.val[e₁.back.val - 1]'(by omega) =
            (rest.drop (to_fold.val - 1)).getLast nonempty := by
          rw [List.getLast_eq_getElem]
          simp only [← remEq, List.getElem_drop, List.length_drop]
          congr 1
          simp [hd, hb', hlen]
          omega
        have tailEq : (e₁.digests.val.drop e₁.front.val).take (b.val - e₁.front.val) =
            (rest.drop (to_fold.val - 1)).dropLast := by
          rw [remEq, List.dropLast_eq_take, remLen, bv]
          congr 1
          omega
        refine ⟨e₂, ?_⟩
        simp only at run
        rw [tailEq, lastEq] at run
        simp only [List.getLast_drop] at run
        rw [bagWith_backward foldTerm (to_fold.val - 1) first rest nonempty]
        rw [if_pos (by omega), if_pos fits]
        simp only [hbk, bind_ok]
        rw [lastEq]
        simp [run, fold_eq, root_eq, onev', drop1]
      · have empty : rest.drop (to_fold.val - 1) = [] := by
          rw [← List.length_eq_zero_iff, remLen]; omega
        refine ⟨e₁, ?_⟩
        rw [bagWith_empty foldTerm _ first rest empty, if_pos (by omega), if_pos fits]
        simp [next_back_none e₁ more, root_eq, onev', drop1]
    | false =>
      obtain ⟨e₂, run⟩ := forward_eq e₁ (List.foldl foldTerm first (rest.take (to_fold.val - 1)))
        inside order
      have whole : (e₁.digests.val.drop e₁.front.val).take (e₁.back.val - e₁.front.val) =
          rest.drop (to_fold.val - 1) := by
        rw [List.take_of_length_le (by rw [remEq, remLen]), remEq]
      refine ⟨e₂, ?_⟩
      rw [whole] at run
      rw [bagWith_forward, if_pos (by omega), if_pos fits]
      simp [run, root_eq, onev', drop1]
  · have fits' : ¬ to_fold.val ≤ L.val.length - 1 + 1 := by omega
    refine ⟨e₁, ?_⟩
    rw [if_neg (by omega), if_neg fits]

/-! ## Sibling counts and the layout -/

/-- A subtree outside the queried range counts as one sibling. -/
theorem siblings_outside (w s loc e : Std.U64) (fits : s.val + w.val < 2 ^ 63)
    (off : s.val + w.val ≤ loc.val ∨ e.val ≤ s.val) :
    reconstruct.siblings w s loc e = RustM.ok 1#usize := by
  obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
  rw [reconstruct.siblings.eq_def]
  simp only [hstop, bind_ok]
  by_cases before : stop.val ≤ loc.val
  · simp [before]
  · have after : e.val ≤ s.val := by omega
    simp [before, after]

/-- A perfect subtree that holds the one queried location needs one sibling per level. -/
theorem siblings_single (n : Nat) : ∀ (w s loc e : Std.U64), w.val = 2 ^ n →
    s.val + w.val < 2 ^ 63 → s.val ≤ loc.val → loc.val < s.val + w.val → e.val = loc.val + 1 →
    ∃ c : Std.Usize, reconstruct.siblings w s loc e = RustM.ok c ∧ c.val = n := by
  induction n with
  | zero =>
    intro w s loc e width fits low high finish
    refine ⟨0#usize, ?_, rfl⟩
    obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
    rw [reconstruct.siblings.eq_def]
    simp only [hstop, bind_ok]
    have c1 : ¬ stop.val ≤ loc.val := by omega
    have c2 : ¬ e.val ≤ s.val := by omega
    have c3 : w = 1#u64 := by scalar_tac
    simp [c1, c2, c3]
  | succ n ih =>
    intro w s loc e width fits low high finish
    have one : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have double : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    have short : n + 1 < 63 := by
      by_contra tall
      have : 2 ^ 63 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
    have c1 : ¬ stop.val ≤ loc.val := by omega
    have c2 : ¬ e.val ≤ s.val := by omega
    have c3 : ¬ w = 1#u64 := by intro h; subst h; simp at width <;> omega
    obtain ⟨half, hhalf, halfv⟩ := UScalar.div_spec w (y := 2#u64) (by decide)
    have halfv' : half.val = 2 ^ n := by simp at halfv; omega
    obtain ⟨mid, hmid, midv⟩ := add_ok s half (by scalar_tac)
    by_cases side : loc.val < mid.val
    · obtain ⟨l, hl, lv⟩ := ih half s loc e halfv' (by omega) low (by omega) finish
      have r := siblings_outside half mid loc e (by omega) (Or.inr (by omega))
      obtain ⟨c, hc, cv⟩ := add_ok l 1#usize (by scalar_tac)
      refine ⟨c, ?_, by simp at cv; omega⟩
      rw [reconstruct.siblings.eq_def]
      simp only [hstop, bind_ok]
      simp [c1, c2, c3, hhalf, hl, hmid, r, hc]
    · have l := siblings_outside half s loc e (by omega) (Or.inl (by omega))
      obtain ⟨r, hr, rv⟩ := ih half mid loc e halfv' (by omega) (by omega) (by omega) finish
      obtain ⟨c, hc, cv⟩ := add_ok 1#usize r (by scalar_tac)
      refine ⟨c, ?_, by simp at cv; omega⟩
      rw [reconstruct.siblings.eq_def]
      simp only [hstop, bind_ok]
      simp [c1, c2, c3, hhalf, l, hmid, hr, hc]

/-- Saturating subtraction on natural numbers. -/
theorem saturating_val (x y : Std.Usize) :
    (UScalar.saturating_sub x y).val = x.val - y.val := by
  rw [← UScalar.bv_toNat (UScalar.saturating_sub x y)]
  simp only [UScalar.saturating_sub]
  simp only [Nat.zero_max, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.bv.isLt)

theorem saturating_ok (x y : Std.Usize) :
    CoreModels.core.num.Usize.saturating_sub x y = RustM.ok (UScalar.saturating_sub x y) := by
  simp [CoreModels.core.num.Usize.saturating_sub, rust_primitives.arithmetic.saturating_sub_usize]

/-- The layout of a proof whose range overlaps one peak, with `before` peaks before it and
`after` after it. -/
theorem layout_some (before after inactive : Std.Usize) (backward : Bool)
    (small : before.val + 1 + after.val ≤ 64) (fits : inactive.val ≤ before.val + 1 + after.val) :
    ∃ l : reconstruct.Layout, reconstruct.Layout.new before 1#usize after inactive backward =
      RustM.ok (.Some l) ∧ l.before = before ∧ l.overlapping = 1#usize ∧ l.after = after ∧
      l.fold.val = (if backward then min inactive.val before.val else before.val) ∧
      l.individual_after.val =
        (if backward then min (inactive.val - (before.val + 1)) after.val else after.val) := by
  obtain ⟨i, hi, iv⟩ := add_ok before 1#usize (by scalar_tac)
  obtain ⟨t, ht, tv⟩ := add_ok i after (by scalar_tac)
  have keep : ¬ t.val < inactive.val := by scalar_tac
  cases backward with
  | false =>
    refine ⟨⟨before, 1#usize, after, before, after⟩, ?_, rfl, rfl, rfl, by simp, by simp⟩
    simp [reconstruct.Layout.new, hi, ht, keep]
  | true =>
    have sat := saturating_val inactive i
    refine ⟨⟨before, 1#usize, after,
      if inactive.val < before.val then inactive else before,
      if (UScalar.saturating_sub inactive i).val < after.val then UScalar.saturating_sub inactive i
      else after⟩, ?_, rfl, rfl, rfl, ?_, ?_⟩
    · by_cases lower : inactive.val < before.val <;>
        by_cases sooner : (UScalar.saturating_sub inactive i).val < after.val <;>
        simp [reconstruct.Layout.new, hi, ht, keep, saturating_ok, lower, sooner]
    · by_cases lower : inactive.val < before.val <;> simp [lower] <;> omega
    · by_cases sooner : (UScalar.saturating_sub inactive i).val < after.val <;>
        simp [sooner] <;> simp [sat, iv] at sooner ⊢ <;> omega

/-- Too large an inactive boundary has no layout. -/
theorem layout_none (before after inactive : Std.Usize) (backward : Bool)
    (small : before.val + 1 + after.val ≤ 64) (over : before.val + 1 + after.val < inactive.val) :
    reconstruct.Layout.new before 1#usize after inactive backward = RustM.ok .None := by
  obtain ⟨i, hi, iv⟩ := add_ok before 1#usize (by scalar_tac)
  obtain ⟨t, ht, tv⟩ := add_ok i after (by scalar_tac)
  have drop : t.val < inactive.val := by scalar_tac
  simp [reconstruct.Layout.new, hi, ht, drop]

/-- Where the parts of the digest list start, for a layout of at most 64 peaks. -/
structure Offsets (l : reconstruct.Layout) where
  /-- One if a prefix accumulator is listed. -/
  fold : Nat
  /-- One if a suffix accumulator is listed. -/
  suffix : Nat
  fold_eq : fold = if l.fold.val = 0 then 0 else 1
  suffix_eq : suffix = if l.individual_after.val < l.after.val then 1 else 0

/-- The extracted offset functions, on a layout of at most 64 peaks whose fold and individual
counts fit their groups. -/
theorem offsets_ok (l : reconstruct.Layout) (small : l.before.val + l.after.val ≤ 64)
    (fold : l.fold.val ≤ l.before.val) (individual : l.individual_after.val ≤ l.after.val) :
    reconstruct.Layout.fold_digests l =
        RustM.ok (if l.fold.val = 0 then 0#usize else 1#usize) ∧
      reconstruct.Layout.suffix_digests l =
        RustM.ok (if l.individual_after.val < l.after.val then 1#usize else 0#usize) ∧
      (∃ a, reconstruct.Layout.after_start l = RustM.ok a ∧
        a.val = (if l.fold.val = 0 then 0 else 1) + (l.before.val - l.fold.val)) ∧
      (∃ a, reconstruct.Layout.suffix_start l = RustM.ok a ∧
        a.val = (if l.fold.val = 0 then 0 else 1) + (l.before.val - l.fold.val) +
          l.individual_after.val) ∧
      (∃ a, reconstruct.Layout.siblings_start l = RustM.ok a ∧
        a.val = (if l.fold.val = 0 then 0 else 1) + (l.before.val - l.fold.val) +
          l.individual_after.val + (if l.individual_after.val < l.after.val then 1 else 0)) := by
  have fd : reconstruct.Layout.fold_digests l =
      RustM.ok (if l.fold.val = 0 then 0#usize else 1#usize) := by
    unfold reconstruct.Layout.fold_digests
    by_cases z : l.fold.val = 0
    · have : l.fold = 0#usize := by scalar_tac
      simp [this, z]
    · have : ¬ l.fold = 0#usize := by scalar_tac
      simp [this, z]
  have sd : reconstruct.Layout.suffix_digests l =
      RustM.ok (if l.individual_after.val < l.after.val then 1#usize else 0#usize) := by
    unfold reconstruct.Layout.suffix_digests
    by_cases z : l.individual_after.val < l.after.val
    · have : l.individual_after < l.after := z
      simp [this, z]
    · have : ¬ l.individual_after < l.after := z
      simp [this, z]
  have fv : (if l.fold.val = 0 then 0#usize else 1#usize).val =
      if l.fold.val = 0 then 0 else 1 := by
    split <;> simp
  have gv : (if l.individual_after.val < l.after.val then 1#usize else 0#usize).val =
      if l.individual_after.val < l.after.val then 1 else 0 := by
    split <;> simp
  obtain ⟨d, hd, dv⟩ := sub_ok l.before l.fold fold
  obtain ⟨a, ha, av⟩ := add_ok (if l.fold.val = 0 then 0#usize else 1#usize) d
    (by rw [fv]; split <;> scalar_tac)
  have hAfter : reconstruct.Layout.after_start l = RustM.ok a := by
    simp only [reconstruct.Layout.after_start, reconstruct.Layout.prefix_start, fd, hd, ha,
      bind_ok]
  have aSmall : a.val ≤ 65 := by rw [av, fv, dv]; split <;> omega
  obtain ⟨b, hb, bv⟩ := add_ok a l.individual_after (by scalar_tac)
  have hSuffix : reconstruct.Layout.suffix_start l = RustM.ok b := by
    simp only [reconstruct.Layout.suffix_start, hAfter, hb, bind_ok]
  have bSmall : b.val ≤ 129 := by rw [bv]; omega
  obtain ⟨c, hc, cv⟩ := add_ok b
    (if l.individual_after.val < l.after.val then 1#usize else 0#usize)
    (by rw [gv]; split <;> scalar_tac)
  have hSiblings : reconstruct.Layout.siblings_start l = RustM.ok c := by
    simp only [reconstruct.Layout.siblings_start, hSuffix, sd, hc, bind_ok]
  exact ⟨fd, sd, ⟨a, hAfter, by rw [av, fv, dv]⟩, ⟨b, hSuffix, by rw [bv, av, fv, dv]⟩,
    ⟨c, hSiblings, by rw [cv, bv, av, fv, dv, gv]⟩⟩

/-- The count of inactive peaks left after the prefix accumulator replaces the folded ones. -/
theorem inactive_after_fold_ok (l : reconstruct.Layout) (inactive : Std.Usize)
    (small : inactive.val ≤ 64) :
    ∃ k, reconstruct.Layout.inactive_after_fold l inactive = RustM.ok k ∧
      k.val = if l.fold.val = 0 then inactive.val else inactive.val - l.fold.val + 1 := by
  unfold reconstruct.Layout.inactive_after_fold
  by_cases z : l.fold.val = 0
  · have : l.fold = 0#usize := by scalar_tac
    exact ⟨inactive, by simp [this], by simp [z]⟩
  · have : ¬ l.fold = 0#usize := by scalar_tac
    obtain ⟨k, hk, kv⟩ := add_ok (UScalar.saturating_sub inactive l.fold) 1#usize
      (by rw [saturating_val]; scalar_tac)
    exact ⟨k, by simp [this, saturating_ok, hk], by rw [kv, saturating_val]; simp [z]⟩

/-! ## The peaks of a structure -/

/-- Repeated reads with `next` from `st` yield `ps`, then nothing. -/
inductive Yields {P : Type} (next : P → RustM (core.option.Option (Std.U64 × Std.U32) × P)) :
    P → List (Std.U64 × Std.U32) → Prop
  /-- No peak is left. -/
  | nil {st st' : P} : next st = RustM.ok (.None, st') → Yields next st []
  /-- The next peak is `p`, and `ps` follow it. -/
  | cons {st st' : P} {p : Std.U64 × Std.U32} {ps : List (Std.U64 × Std.U32)} :
      next st = RustM.ok (.Some p, st') → Yields next st' ps → Yields next st (p :: ps)

/-- The leaves the peaks cover. -/
def span (ps : List (Std.U64 × Std.U32)) : Nat := (ps.map fun p => 2 ^ p.2.val).sum

theorem span_append (a b : List (Std.U64 × Std.U32)) : span (a ++ b) = span a + span b := by
  simp [span]

theorem span_cons (q : Std.U64) (h : Std.U32) (ps : List (Std.U64 × Std.U32)) :
    span ((q, h) :: ps) = 2 ^ h.val + span ps := by
  simp [span]

/-- Each peak of `ps` is at most 62 high. -/
def Low (ps : List (Std.U64 × Std.U32)) : Prop := ∀ p ∈ ps, p.2.val ≤ 62

theorem width_ok (h : Std.U32) (low : h.val ≤ 62) :
    ∃ w : Std.U64, 1#u64 <<< h = RustM.ok w ∧ w.val = 2 ^ h.val :=
  pow_ok h (by omega)

/-! ## Classifying the peaks -/

section Classify
variable {G P : Type} (geo : reconstruct.Geometry G P)

/-- Peaks wholly before the queried location count as before. -/
theorem classify_before (pre : List (Std.U64 × Std.U32)) :
    ∀ (rest : List (Std.U64 × Std.U32)) (st : P) (loc e : Std.U64)
      (b o a s : Std.Usize) (ls : Std.U64),
    Yields geo.PeaksInst.next st (pre ++ rest) → Low pre → ls.val + span pre ≤ loc.val →
    b.val + pre.length ≤ 64 →
    ∃ (st' : P) (b' : Std.Usize) (ls' : Std.U64), Yields geo.PeaksInst.next st' rest ∧
      b'.val = b.val + pre.length ∧ ls'.val = ls.val + span pre ∧
      reconstruct.reconstruct_loop geo st loc e b o a s ls =
        reconstruct.reconstruct_loop geo st' loc e b' o a s ls' := by
  induction pre with
  | nil =>
    intro rest st loc e b o a s ls yields _ _ _
    exact ⟨st, b, ls, yields, by simp, by simp [span], rfl⟩
  | cons p pre ih =>
    intro rest st loc e b o a s ls yields low below count
    obtain ⟨pp, ph⟩ := p
    cases yields with
    | cons hnext tail =>
      rename_i st₁
      have hp : ph.val ≤ 62 := low (pp, ph) (by simp)
      obtain ⟨w, hw, wv⟩ := width_ok ph hp
      rw [span_cons] at below
      simp only [List.length_cons] at count
      obtain ⟨le, hle, lev⟩ := add_ok ls w (by scalar_tac)
      have bSmall : b.val + 1 ≤ 64 := by omega
      obtain ⟨b₁, hb₁, b₁v⟩ := add_ok b 1#usize (by scalar_tac)
      have b₁v' : b₁.val = b.val + 1 := by simpa using b₁v
      have before : le.val ≤ loc.val := by omega
      have step : reconstruct.reconstruct_loop.body geo loc e st b o a s ls =
          RustM.ok (.cont (st₁, b₁, o, a, s, le)) := by
        simp [reconstruct.reconstruct_loop.body, hnext, hw, hle, before, hb₁]
      obtain ⟨st', b', ls', yields', bv, lsv, run⟩ := ih rest st₁ loc e b₁ o a s le tail
        (fun q hq => low q (by simp [hq])) (by omega) (by omega)
      refine ⟨st', b', ls', yields', by simp only [List.length_cons]; omega,
        by rw [lsv, lev, wv, span_cons]; omega, ?_⟩
      unfold reconstruct.reconstruct_loop
      rw [loop_cont _ _ _ step]
      unfold reconstruct.reconstruct_loop at run
      exact run

/-- Peaks wholly after the queried location count as after, up to the last one. -/
theorem classify_after (post : List (Std.U64 × Std.U32)) :
    ∀ (st : P) (loc e : Std.U64) (b o a s : Std.Usize) (ls : Std.U64),
    Yields geo.PeaksInst.next st post → Low post → e.val ≤ ls.val → loc.val < e.val →
    ls.val + span post < 2 ^ 63 → a.val + post.length ≤ 64 →
    ∃ a' : Std.Usize, a'.val = a.val + post.length ∧
      reconstruct.reconstruct_loop geo st loc e b o a s ls = RustM.ok (b, o, a', s) := by
  induction post with
  | nil =>
    intro st loc e b o a s ls yields _ _ _ _ _
    cases yields with
    | nil hnext =>
      refine ⟨a, by simp, ?_⟩
      have step : reconstruct.reconstruct_loop.body geo loc e st b o a s ls =
          RustM.ok (.done (b, o, a, s)) := by
        simp [reconstruct.reconstruct_loop.body, hnext]
      unfold reconstruct.reconstruct_loop
      exact loop_done _ _ _ step
  | cons p post ih =>
    intro st loc e b o a s ls yields low after order fits count
    obtain ⟨pp, ph⟩ := p
    cases yields with
    | cons hnext tail =>
      rename_i st₁
      have hp : ph.val ≤ 62 := low (pp, ph) (by simp)
      obtain ⟨w, hw, wv⟩ := width_ok ph hp
      rw [span_cons] at fits
      simp only [List.length_cons] at count
      have one : 1 ≤ 2 ^ ph.val := Nat.one_le_two_pow
      obtain ⟨le, hle, lev⟩ := add_ok ls w (by scalar_tac)
      have aSmall : a.val + 1 ≤ 64 := by omega
      obtain ⟨a₁, ha₁, a₁v⟩ := add_ok a 1#usize (by scalar_tac)
      have a₁v' : a₁.val = a.val + 1 := by simpa using a₁v
      have notBefore : ¬ le.val ≤ loc.val := by omega
      have isAfter : e.val ≤ ls.val := after
      have step : reconstruct.reconstruct_loop.body geo loc e st b o a s ls =
          RustM.ok (.cont (st₁, b, o, a₁, s, le)) := by
        simp [reconstruct.reconstruct_loop.body, hnext, hw, hle, notBefore, isAfter, ha₁]
      obtain ⟨a', av, run⟩ := ih st₁ loc e b o a₁ s le tail (fun q hq => low q (by simp [hq]))
        (by omega) order (by omega) (by omega)
      refine ⟨a', by simp only [List.length_cons]; omega, ?_⟩
      unfold reconstruct.reconstruct_loop
      rw [loop_cont _ _ _ step]
      unfold reconstruct.reconstruct_loop at run
      exact run

/-- The classification of a structure whose peak `(pos, h)` holds the queried location: the
peaks before it, one overlapping peak needing `h` siblings, and the peaks after it. -/
theorem classify_single (pre post : List (Std.U64 × Std.U32)) (pos : Std.U64) (h : Std.U32)
    (st : P) (loc e : Std.U64)
    (yields : Yields geo.PeaksInst.next st (pre ++ (pos, h) :: post))
    (low : Low (pre ++ (pos, h) :: post)) (finish : e.val = loc.val + 1)
    (inside : span pre ≤ loc.val ∧ loc.val < span pre + 2 ^ h.val)
    (fits : span (pre ++ (pos, h) :: post) < 2 ^ 63)
    (count : pre.length + 1 + post.length ≤ 64) :
    ∃ b a s : Std.Usize, reconstruct.reconstruct_loop geo st loc e 0#usize 0#usize 0#usize
      0#usize 0#u64 = RustM.ok (b, 1#usize, a, s) ∧ b.val = pre.length ∧ a.val = post.length ∧
      s.val = h.val := by
  rw [span_append, span_cons] at fits
  obtain ⟨st₁, b, ls, yields₁, bv, lsv, run₁⟩ := classify_before geo pre ((pos, h) :: post) st
    loc e 0#usize 0#usize 0#usize 0#usize 0#u64 yields (fun q hq => low q (by simp [hq]))
    (by simp; omega) (by simp; omega)
  cases yields₁ with
  | cons hnext tail =>
    rename_i st₂
    have hh : h.val ≤ 62 := low (pos, h) (by simp)
    obtain ⟨w, hw, wv⟩ := width_ok h hh
    simp at lsv bv
    obtain ⟨le, hle, lev⟩ := add_ok ls w (by scalar_tac)
    have notBefore : ¬ le.val ≤ loc.val := by omega
    have notAfter : ¬ e.val ≤ ls.val := by omega
    obtain ⟨c, hc, cv⟩ := siblings_single h.val w ls loc e wv (by omega) (by omega) (by omega)
      finish
    obtain ⟨s₁, hs₁, s₁v⟩ := add_ok 0#usize c (by scalar_tac)
    obtain ⟨o₁, ho₁, o₁v⟩ := add_ok 0#usize 1#usize (by scalar_tac)
    have o₁e : o₁ = 1#usize := by scalar_tac
    subst o₁e
    have step : reconstruct.reconstruct_loop.body geo loc e st₁ b 0#usize 0#usize 0#usize ls =
        RustM.ok (.cont (st₂, b, 1#usize, 0#usize, s₁, le)) := by
      simp [reconstruct.reconstruct_loop.body, hnext, hw, hle, notBefore, notAfter, hc, hs₁, ho₁]
    obtain ⟨a, av, run₂⟩ := classify_after geo post st₂ loc e b 1#usize 0#usize s₁ le tail
      (fun q hq => low q (by simp [hq])) (by omega) (by omega) (by omega) (by simp; omega)
    refine ⟨b, a, s₁, ?_, bv, by simpa using av, by simp at s₁v; omega⟩
    rw [run₁]
    unfold reconstruct.reconstruct_loop
    rw [loop_cont _ _ _ step]
    unfold reconstruct.reconstruct_loop at run₂
    exact run₂

end Classify

/-! ## Listing the peak digests -/

/-- The element source of a proof of one item. -/
abbrev single := reconstruct.Single.Insts.CoreIterTraitsIteratorIteratorElement
/-- The element as bytes. -/
abbrev element := reconstruct.Element.Insts.CoreConvertAsRefSliceU8
/-- The collector that records nothing. -/
abbrev noCollect := Tuple.Insts.Commonware_symbolicTraversalCollect Bytes

/-- A vector of digests, as the extraction models it: a slice. -/
abbrev DigestVec := CoreModels.alloc.vec.Vec Bytes

/-- The digests in a vector. -/
def items (v : DigestVec) : List Bytes := Slice.val v

theorem push_ok (v : DigestVec) (d : Bytes) (room : (items v).length < 1000) :
    ∃ w : DigestVec, CoreModels.alloc.vec.Vec.push v d = RustM.ok w ∧ items w = items v ++ [d] := by
  have fits : (Slice.val v ++ [d]).length ≤ Usize.max := by
    simp [items] at room; simp; scalar_tac
  refine ⟨Slice.from (Slice.val v ++ [d]) fits, ?_, by simp [items]⟩
  have lt : (Slice.val v).length < Usize.max := by simp at fits; omega
  simp [CoreModels.alloc.vec.Vec.push, rust_primitives.sequence.seq_push, lt]

@[simp] theorem opening_eta {N : Type} (o : traversal.Opening N reconstruct.Single Unit Bytes) :
    (⟨o.nodes, o.elements, o.siblings, o.cursor, o.collected⟩ :
      traversal.Opening N reconstruct.Single Unit Bytes) = o :=
  rfl

theorem peak_ok {N : Type} (nodes : traversal.Nodes N Bytes)
    (o : traversal.Opening N reconstruct.Single Unit Bytes) (p : Std.U64) (d : Bytes) :
    traversal.Opening.peak nodes noCollect o p d = RustM.ok o := by
  simp [traversal.Opening.peak, Tuple.Insts.Commonware_symbolicTraversalCollect.peak]

section List
variable {G P N : Type} (geo : reconstruct.Geometry G P) (nodes : traversal.Nodes N Bytes)

/-- The peak-listing loop with the client's element source and no collector. -/
abbrev listLoop (st : P) (l : reconstruct.Layout) (digests : Slice Bytes) (loc e : Std.U64)
    (o : traversal.Opening N reconstruct.Single Unit Bytes) (v : DigestVec)
    (index : Std.Usize) (ls : Std.U64) :=
  reconstruct.list_peaks_loop geo nodes single element noCollect st l digests loc e o.nodes
    o.elements o.siblings o.cursor o.collected v index ls

/-- Peaks before the range that fold into the prefix accumulator list nothing. -/
theorem list_fold (seg : List (Std.U64 × Std.U32)) :
    ∀ (rest : List (Std.U64 × Std.U32)) (st : P) (l : reconstruct.Layout)
      (digests : Slice Bytes) (loc e : Std.U64) (o : traversal.Opening N reconstruct.Single Unit Bytes)
      (v : DigestVec) (index : Std.Usize) (ls : Std.U64),
    Yields geo.PeaksInst.next st (seg ++ rest) → Low seg →
    index.val + seg.length ≤ l.fold.val → l.fold.val ≤ l.before.val → l.before.val ≤ 64 →
    ls.val + span seg < 2 ^ 63 →
    ∃ (st' : P) (index' : Std.Usize) (ls' : Std.U64), Yields geo.PeaksInst.next st' rest ∧
      index'.val = index.val + seg.length ∧ ls'.val = ls.val + span seg ∧
      listLoop geo nodes st l digests loc e o v index ls =
        listLoop geo nodes st' l digests loc e o v index' ls' := by
  induction seg with
  | nil =>
    intro rest st l digests loc e o v index ls yields _ _ _ _ _
    exact ⟨st, index, ls, yields, by simp, by simp [span], rfl⟩
  | cons p seg ih =>
    intro rest st l digests loc e o v index ls yields low below order small fits
    obtain ⟨pp, ph⟩ := p
    cases yields with
    | cons hnext tail =>
      rename_i st₁
      have hp : ph.val ≤ 62 := low (pp, ph) (by simp)
      obtain ⟨w, hw, wv⟩ := width_ok ph hp
      rw [span_cons] at fits
      simp only [List.length_cons] at below
      obtain ⟨le, hle, lev⟩ := add_ok ls w (by scalar_tac)
      obtain ⟨i₁, hi₁, i₁v⟩ := add_ok index 1#usize (by scalar_tac)
      have isBefore : index.val < l.before.val := by omega
      have folded : ¬ l.fold.val ≤ index.val := by omega
      have step : reconstruct.list_peaks_loop.body geo nodes single element noCollect l digests
          loc e st o.nodes o.elements o.siblings o.cursor o.collected v index ls =
          RustM.ok (.cont (st₁, o.nodes, o.elements, o.siblings, o.cursor, o.collected, v, i₁,
            le)) := by
        simp [reconstruct.list_peaks_loop.body, hnext, hw, isBefore, folded, hle, hi₁]
      obtain ⟨st', index', ls', yields', iv, lsv, run⟩ := ih rest st₁ l digests loc e o v i₁ le
        tail (fun q hq => low q (by simp [hq])) (by simp at i₁v; omega) order small (by omega)
      refine ⟨st', index', ls', yields', by simp at i₁v; simp only [List.length_cons]; omega,
        by rw [lsv, lev, wv, span_cons]; omega, ?_⟩
      unfold listLoop reconstruct.list_peaks_loop
      rw [loop_cont _ _ _ step]
      unfold listLoop reconstruct.list_peaks_loop at run
      exact run

/-- Active peaks before the range list their digests, which follow the prefix accumulator in
order. -/
theorem list_prefix (seg : List (Std.U64 × Std.U32)) :
    ∀ (rest : List (Std.U64 × Std.U32)) (st : P) (l : reconstruct.Layout) (start : Std.Usize)
      (digests : Slice Bytes) (loc e : Std.U64)
      (o : traversal.Opening N reconstruct.Single Unit Bytes)
      (v : DigestVec) (index : Std.Usize) (ls : Std.U64),
    Yields geo.PeaksInst.next st (seg ++ rest) → Low seg →
    reconstruct.Layout.prefix_start l = RustM.ok start →
    l.fold.val ≤ index.val → index.val + seg.length ≤ l.before.val → l.before.val ≤ 64 →
    start.val + l.before.val - l.fold.val ≤ digests.val.length →
    (items v).length + seg.length ≤ 200 → ls.val + span seg < 2 ^ 63 →
    ∃ (st' : P) (index' : Std.Usize) (ls' : Std.U64) (v' : DigestVec),
      Yields geo.PeaksInst.next st' rest ∧
      index'.val = index.val + seg.length ∧ ls'.val = ls.val + span seg ∧
      items v' = items v ++
        (digests.val.drop (start.val + index.val - l.fold.val)).take seg.length ∧
      listLoop geo nodes st l digests loc e o v index ls =
        listLoop geo nodes st' l digests loc e o v' index' ls' := by
  induction seg with
  | nil =>
    intro rest st l start digests loc e o v index ls yields _ _ _ _ _ _ _ _
    exact ⟨st, index, ls, v, yields, by simp, by simp [span], by simp, rfl⟩
  | cons p seg ih =>
    intro rest st l start digests loc e o v index ls yields low hstart order below small inside
      room fits
    obtain ⟨pp, ph⟩ := p
    cases yields with
    | cons hnext tail =>
      rename_i st₁
      have hp : ph.val ≤ 62 := low (pp, ph) (by simp)
      obtain ⟨w, hw, wv⟩ := width_ok ph hp
      rw [span_cons] at fits
      simp only [List.length_cons] at below room
      obtain ⟨le, hle, lev⟩ := add_ok ls w (by scalar_tac)
      obtain ⟨i₁, hi₁, i₁v⟩ := add_ok index 1#usize (by scalar_tac)
      have isBefore : index.val < l.before.val := by omega
      have active : l.fold.val ≤ index.val := order
      obtain ⟨k, hk, kv⟩ := sub_ok index l.fold order
      obtain ⟨j, hj, jv⟩ := add_ok start k (by scalar_tac)
      have jIn : j.val < digests.val.length := by omega
      have get := index_ok digests j jIn
      obtain ⟨v₁, hv₁, v₁v⟩ := push_ok v (digests.val[j.val]'jIn) (by omega)
      have step : reconstruct.list_peaks_loop.body geo nodes single element noCollect l digests
          loc e st o.nodes o.elements o.siblings o.cursor o.collected v index ls =
          RustM.ok (.cont (st₁, o.nodes, o.elements, o.siblings, o.cursor, o.collected, v₁, i₁,
            le)) := by
        simp [reconstruct.list_peaks_loop.body, hnext, hw, isBefore, active, hstart, hk, hj,
          get, peak_ok, hv₁, hle, hi₁]
      obtain ⟨st', index', ls', v', yields', iv, lsv, vv, run⟩ := ih rest st₁ l start digests
        loc e o v₁ i₁ le tail (fun q hq => low q (by simp [hq])) hstart
        (by simp at i₁v; omega) (by simp at i₁v; omega) small inside (by rw [v₁v]; simp; omega)
        (by omega)
      refine ⟨st', index', ls', v', yields', by simp at i₁v; simp only [List.length_cons]; omega,
        by rw [lsv, lev, wv, span_cons]; omega, ?_, ?_⟩
      · rw [vv, v₁v, List.append_assoc]
        congr 1
        simp at i₁v
        have shift : start.val + i₁.val - l.fold.val = j.val + 1 := by omega
        have at_j : start.val + index.val - l.fold.val = j.val := by omega
        rw [shift, at_j, List.drop_eq_getElem_cons jIn, List.length_cons, List.take_succ_cons]
        rfl
      · unfold listLoop reconstruct.list_peaks_loop
        rw [loop_cont _ _ _ step]
        unfold listLoop reconstruct.list_peaks_loop at run
        exact run

/-- Active peaks after the range that are listed individually list their digests in order. -/
theorem list_after (seg : List (Std.U64 × Std.U32)) :
    ∀ (rest : List (Std.U64 × Std.U32)) (st : P) (l : reconstruct.Layout) (start : Std.Usize)
      (digests : Slice Bytes) (loc e : Std.U64)
      (o : traversal.Opening N reconstruct.Single Unit Bytes)
      (v : DigestVec) (index : Std.Usize) (ls : Std.U64),
    Yields geo.PeaksInst.next st (seg ++ rest) → Low seg →
    reconstruct.Layout.after_start l = RustM.ok start →
    l.before.val + l.overlapping.val ≤ index.val →
    index.val - l.before.val - l.overlapping.val + seg.length ≤ l.individual_after.val →
    index.val + seg.length ≤ 64 →
    start.val + l.individual_after.val ≤ digests.val.length →
    (items v).length + seg.length ≤ 200 → ls.val + span seg < 2 ^ 63 →
    ∃ (st' : P) (index' : Std.Usize) (ls' : Std.U64) (v' : DigestVec),
      Yields geo.PeaksInst.next st' rest ∧
      index'.val = index.val + seg.length ∧ ls'.val = ls.val + span seg ∧
      items v' = items v ++ (digests.val.drop
        (start.val + (index.val - l.before.val - l.overlapping.val))).take seg.length ∧
      listLoop geo nodes st l digests loc e o v index ls =
        listLoop geo nodes st' l digests loc e o v' index' ls' := by
  induction seg with
  | nil =>
    intro rest st l start digests loc e o v index ls yields _ _ _ _ _ _ _ _
    exact ⟨st, index, ls, v, yields, by simp, by simp [span], by simp, rfl⟩
  | cons p seg ih =>
    intro rest st l start digests loc e o v index ls yields low hstart order below small inside
      room fits
    obtain ⟨pp, ph⟩ := p
    cases yields with
    | cons hnext tail =>
      rename_i st₁
      have hp : ph.val ≤ 62 := low (pp, ph) (by simp)
      obtain ⟨w, hw, wv⟩ := width_ok ph hp
      rw [span_cons] at fits
      simp only [List.length_cons] at below room small
      obtain ⟨le, hle, lev⟩ := add_ok ls w (by scalar_tac)
      obtain ⟨i₁, hi₁, i₁v⟩ := add_ok index 1#usize (by scalar_tac)
      have notBefore : ¬ index.val < l.before.val := by omega
      obtain ⟨bo, hbo, bov⟩ := add_ok l.before l.overlapping (by scalar_tac)
      have notOverlap : ¬ index.val < bo.val := by omega
      obtain ⟨x, hx, xv⟩ := sub_ok index l.before (by omega)
      obtain ⟨off, hoff, offv⟩ := sub_ok x l.overlapping (by omega)
      have listed : off.val < l.individual_after.val := by omega
      obtain ⟨j, hj, jv⟩ := add_ok start off (by scalar_tac)
      have jIn : j.val < digests.val.length := by omega
      have get := index_ok digests j jIn
      obtain ⟨v₁, hv₁, v₁v⟩ := push_ok v (digests.val[j.val]'jIn) (by omega)
      have step : reconstruct.list_peaks_loop.body geo nodes single element noCollect l digests
          loc e st o.nodes o.elements o.siblings o.cursor o.collected v index ls =
          RustM.ok (.cont (st₁, o.nodes, o.elements, o.siblings, o.cursor, o.collected, v₁, i₁,
            le)) := by
        simp [reconstruct.list_peaks_loop.body, hnext, hw, notBefore, hbo, notOverlap, hx, hoff,
          listed, hstart, hj, get, peak_ok, hv₁, hle, hi₁]
      obtain ⟨st', index', ls', v', yields', iv, lsv, vv, run⟩ := ih rest st₁ l start digests
        loc e o v₁ i₁ le tail (fun q hq => low q (by simp [hq])) hstart
        (by simp at i₁v; omega) (by simp at i₁v; omega) (by simp at i₁v; omega) inside
        (by rw [v₁v]; simp; omega) (by omega)
      refine ⟨st', index', ls', v', yields', by simp at i₁v; simp only [List.length_cons]; omega,
        by rw [lsv, lev, wv, span_cons]; omega, ?_, ?_⟩
      · rw [vv, v₁v, List.append_assoc]
        congr 1
        simp at i₁v
        have shift : start.val + (i₁.val - l.before.val - l.overlapping.val) = j.val + 1 := by
          omega
        have at_j : start.val + (index.val - l.before.val - l.overlapping.val) = j.val := by
          omega
        rw [shift, at_j, List.drop_eq_getElem_cons jIn, List.length_cons, List.take_succ_cons]
        rfl
      · unfold listLoop reconstruct.list_peaks_loop
        rw [loop_cont _ _ _ step]
        unfold listLoop reconstruct.list_peaks_loop at run
        exact run

/-- Active peaks after the range that collapse into the suffix accumulator list nothing, and
the loop ends after the last peak. -/
theorem list_suffix (seg : List (Std.U64 × Std.U32)) :
    ∀ (st : P) (l : reconstruct.Layout) (digests : Slice Bytes) (loc e : Std.U64)
      (o : traversal.Opening N reconstruct.Single Unit Bytes)
      (v : DigestVec) (index : Std.Usize) (ls : Std.U64),
    Yields geo.PeaksInst.next st seg → Low seg →
    l.before.val + l.overlapping.val + l.individual_after.val ≤ index.val →
    index.val + seg.length ≤ 64 → ls.val + span seg < 2 ^ 63 →
    listLoop geo nodes st l digests loc e o v index ls = RustM.ok (.Ok (), o, v) := by
  induction seg with
  | nil =>
    intro st l digests loc e o v index ls yields _ _ _ _
    cases yields with
    | nil hnext =>
      have step : reconstruct.list_peaks_loop.body geo nodes single element noCollect l digests
          loc e st o.nodes o.elements o.siblings o.cursor o.collected v index ls =
          RustM.ok (.done (.Ok (), o, v)) := by
        simp [reconstruct.list_peaks_loop.body, hnext]
      unfold listLoop reconstruct.list_peaks_loop
      exact loop_done _ _ _ step
  | cons p seg ih =>
    intro st l digests loc e o v index ls yields low order small fits
    obtain ⟨pp, ph⟩ := p
    cases yields with
    | cons hnext tail =>
      rename_i st₁
      have hp : ph.val ≤ 62 := low (pp, ph) (by simp)
      obtain ⟨w, hw, wv⟩ := width_ok ph hp
      rw [span_cons] at fits
      simp only [List.length_cons] at small
      obtain ⟨le, hle, lev⟩ := add_ok ls w (by scalar_tac)
      obtain ⟨i₁, hi₁, i₁v⟩ := add_ok index 1#usize (by scalar_tac)
      have notBefore : ¬ index.val < l.before.val := by omega
      obtain ⟨bo, hbo, bov⟩ := add_ok l.before l.overlapping (by scalar_tac)
      have notOverlap : ¬ index.val < bo.val := by omega
      obtain ⟨x, hx, xv⟩ := sub_ok index l.before (by omega)
      obtain ⟨off, hoff, offv⟩ := sub_ok x l.overlapping (by omega)
      have collapsed : ¬ off.val < l.individual_after.val := by omega
      have step : reconstruct.list_peaks_loop.body geo nodes single element noCollect l digests
          loc e st o.nodes o.elements o.siblings o.cursor o.collected v index ls =
          RustM.ok (.cont (st₁, o.nodes, o.elements, o.siblings, o.cursor, o.collected, v, i₁,
            le)) := by
        simp [reconstruct.list_peaks_loop.body, hnext, hw, notBefore, hbo, notOverlap, hx, hoff,
          collapsed, hle, hi₁]
      have run := ih st₁ l digests loc e o v i₁ le tail (fun q hq => low q (by simp [hq]))
        (by simp at i₁v; omega) (by simp at i₁v; omega) (by omega)
      unfold listLoop reconstruct.list_peaks_loop
      rw [loop_cont _ _ _ step]
      unfold listLoop reconstruct.list_peaks_loop at run
      exact run

/-- The production traversal backend over `nodes`, the client's element source and no
collector. -/
abbrev backend := traversal.Opening.Insts.Commonware_symbolicTraversalBackend nodes single element
  noCollect

/-- The peak holding the range is rebuilt by the traversal; its digest is listed, or the
traversal's failure ends the loop. -/
theorem list_target (st st₁ : P) (pos : Std.U64) (h : Std.U32) (l : reconstruct.Layout)
    (digests : Slice Bytes) (loc e : Std.U64)
    (o : traversal.Opening N reconstruct.Single Unit Bytes) (v : DigestVec) (index : Std.Usize)
    (ls w : Std.U64) (hnext : geo.PeaksInst.next st = RustM.ok (.Some (pos, h), st₁))
    (hw : 1#u64 <<< h = RustM.ok w) (fits : ls.val + w.val < 2 ^ 63)
    (at_target : index.val = l.before.val) (one : l.overlapping.val = 1) (small : index.val < 64) :
    ∃ (le : Std.U64) (i₁ : Std.Usize), le.val = ls.val + w.val ∧ i₁.val = index.val + 1 ∧
      listLoop geo nodes st l digests loc e o v index ls = (do
        let (r, o₁) ← traversal.reconstruct (backend nodes) o pos w ls loc e
        match r with
        | .Ok d => do
          let v₁ ← CoreModels.alloc.vec.Vec.push v d
          listLoop geo nodes st₁ l digests loc e o₁ v₁ i₁ le
        | .Err err => do
          let x ← reconstruct.missing err
          RustM.ok (.Err x, o₁, v)) := by
  obtain ⟨le, hle, lev⟩ := add_ok ls w (by scalar_tac)
  obtain ⟨i₁, hi₁, i₁v⟩ := add_ok index 1#usize (by scalar_tac)
  refine ⟨le, i₁, lev, by simpa using i₁v, ?_⟩
  have notBefore : ¬ index.val < l.before.val := by omega
  obtain ⟨bo, hbo, bov⟩ := add_ok l.before l.overlapping (by scalar_tac)
  have overlaps : index.val < bo.val := by omega
  have notBefore' : ¬ index < l.before := notBefore
  have overlaps' : index < bo := overlaps
  unfold listLoop reconstruct.list_peaks_loop
  rw [loop.eq_def]
  simp [reconstruct.list_peaks_loop.body, hnext, hw, notBefore, notBefore', hbo, overlaps,
    overlaps', opening_eta]
  congr 1
  funext x
  obtain ⟨r, o₁⟩ := x
  cases r with
  | Ok d => simp [peak_ok, hle, hi₁]
  | Err err => simp

/-- A vector holding `L`. -/
def vecOf (L : List Bytes) (fits : L.length ≤ Usize.max) : DigestVec := Slice.from L fits

theorem items_vecOf (L : List Bytes) (fits : L.length ≤ Usize.max) :
    items (vecOf L fits) = L := by
  simp [items, vecOf]

theorem vec_new_eq : CoreModels.alloc.vec.Vec.new Bytes = RustM.ok (vecOf [] (by simp)) := by
  simp [CoreModels.alloc.vec.Vec.new, rust_primitives.sequence.seq_empty, vecOf]
  rfl

theorem deref_eq (v : DigestVec) : ∃ S : Slice Bytes,
    CoreModels.alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref v = RustM.ok S ∧
      S.val = items v :=
  ⟨v, by simp [CoreModels.alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref,
    CoreModels.alloc.vec.Vec.as_slice, rust_primitives.sequence.seq_to_slice], rfl⟩

theorem ends_new_eq (L : Slice Bytes) :
    reconstruct.Ends.new L = RustM.ok ⟨L, 0#usize, Slice.len L⟩ := by
  simp [reconstruct.Ends.new, len_ok]

theorem vec_ext {v w : DigestVec} (h : items v = items w) : v = w :=
  Slice.ext _ _ h

/-- The listing pass over all the peaks: the peaks before the range list the digests from the
first individually listed one, then the traversal rebuilds the peak holding the range, and the
peaks after it list the digests from the first individually listed one after the range. -/
theorem list_single (pre post : List (Std.U64 × Std.U32)) (pos : Std.U64) (h : Std.U32) (st : P)
    (l : reconstruct.Layout) (digests : Slice Bytes) (loc e w : Std.U64)
    (prefixStart afterStart : Std.Usize)
    (o : traversal.Opening N reconstruct.Single Unit Bytes) (v : DigestVec)
    (yields : Yields geo.PeaksInst.next st (pre ++ (pos, h) :: post))
    (low : Low (pre ++ (pos, h) :: post))
    (fits : span (pre ++ (pos, h) :: post) < 2 ^ 63)
    (count : pre.length + 1 + post.length ≤ 64)
    (lb : l.before.val = pre.length) (lo : l.overlapping.val = 1) (la : l.after.val = post.length)
    (foldLe : l.fold.val ≤ l.before.val) (indLe : l.individual_after.val ≤ l.after.val)
    (hPrefix : reconstruct.Layout.prefix_start l = RustM.ok prefixStart)
    (hAfter : reconstruct.Layout.after_start l = RustM.ok afterStart)
    (afterv : afterStart.val = prefixStart.val + (l.before.val - l.fold.val))
    (inside : afterStart.val + l.individual_after.val ≤ digests.val.length)
    (hw : 1#u64 <<< h = RustM.ok w) (wv : w.val = 2 ^ h.val)
    (room : (items v).length ≤ 1) :
    ∃ ls : Std.U64, ls.val = span pre ∧
      listLoop geo nodes st l digests loc e o v 0#usize 0#u64 = (do
        let (r, o₁) ← traversal.reconstruct (backend nodes) o pos w ls loc e
        match r with
        | .Ok d => RustM.ok (.Ok (), o₁, vecOf (items v ++
            (digests.val.drop prefixStart.val).take (l.before.val - l.fold.val) ++ [d] ++
            (digests.val.drop afterStart.val).take l.individual_after.val) (by
              simp only [List.length_append, List.length_take, List.length_drop,
                List.length_singleton]; scalar_tac))
        | .Err err => do
          let x ← reconstruct.missing err
          RustM.ok (.Err x, o₁, vecOf (items v ++
            (digests.val.drop prefixStart.val).take (l.before.val - l.fold.val)) (by
              simp only [List.length_append, List.length_take, List.length_drop]; scalar_tac))) := by
  have whole := fits
  rw [span_append, span_cons] at whole
  have split : pre ++ (pos, h) :: post =
      pre.take l.fold.val ++ (pre.drop l.fold.val ++ (pos, h) :: post) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [split] at yields
  have lowAll := low
  have spanSplit : span pre = span (pre.take l.fold.val) + span (pre.drop l.fold.val) := by
    rw [← span_append, List.take_append_drop]
  obtain ⟨st₁, i₁, ls₁, yields₁, i₁v, ls₁v, run₁⟩ := list_fold geo nodes (pre.take l.fold.val)
    (pre.drop l.fold.val ++ (pos, h) :: post) st l digests loc e o v 0#usize 0#u64 yields
    (fun q hq => low q (by simp [List.mem_of_mem_take hq]))
    (by simp only [List.length_take]; simp <;> omega) foldLe (by omega)
    (by have : span (pre.take l.fold.val) ≤ span pre := by rw [spanSplit]; omega
        simp <;> omega)
  have takeLen : (pre.take l.fold.val).length = l.fold.val := by
    rw [List.length_take]; omega
  have i₁f : i₁.val = l.fold.val := by rw [i₁v, takeLen]; simp
  have ls₁f : ls₁.val = span (pre.take l.fold.val) := by rw [ls₁v]; simp
  have dropLen : (pre.drop l.fold.val).length = pre.length - l.fold.val := by simp
  obtain ⟨st₂, i₂, ls₂, v₂, yields₂, i₂v, ls₂v, v₂v, run₂⟩ := list_prefix geo nodes
    (pre.drop l.fold.val) ((pos, h) :: post) st₁ l prefixStart digests loc e o v i₁ ls₁ yields₁
    (fun q hq => low q (by simp [List.mem_of_mem_drop hq])) hPrefix
    (by omega) (by rw [dropLen]; omega) (by omega)
    (by omega) (by simp only [items] at room ⊢; rw [dropLen]; omega)
    (by rw [ls₁f]; rw [spanSplit] at whole; omega)
  have i₂v' : i₂.val = l.before.val := by rw [i₂v, i₁f, dropLen]; omega
  have ls₂v' : ls₂.val = span pre := by rw [ls₂v, ls₁f, spanSplit]
  refine ⟨ls₂, ls₂v', ?_⟩
  cases yields₂ with
  | cons hnext tail =>
    rename_i st₃
    obtain ⟨le, i₃, lev, i₃v, run₃⟩ := list_target geo nodes st₂ st₃ pos h l digests loc e o v₂
      i₂ ls₂ w hnext hw (by omega) i₂v' lo (by omega)
    rw [run₁, run₂, run₃]
    congr 1
    funext x
    obtain ⟨r, o₁⟩ := x
    have v₂items : items v₂ = items v ++
        (digests.val.drop prefixStart.val).take (l.before.val - l.fold.val) := by
      rw [v₂v, i₁f, dropLen]
      congr 3
      · omega
      · omega
    cases r with
    | Ok d =>
      have v₂len : (items v₂).length ≤ 1 + pre.length := by
        rw [v₂items, List.length_append]
        have := List.length_take_le (l.before.val - l.fold.val) (digests.val.drop prefixStart.val)
        omega
      obtain ⟨v₃, hv₃, v₃v⟩ := push_ok v₂ d (by omega)
      have i₃f : i₃.val = l.before.val + 1 := by rw [i₃v, i₂v']
      have splitPost : post = post.take l.individual_after.val ++ post.drop l.individual_after.val :=
        (List.take_append_drop _ _).symm
      have tail' := tail
      rw [splitPost] at tail'
      obtain ⟨st₄, i₄, ls₄, v₄, yields₄, i₄v, ls₄v, v₄v, run₄⟩ := list_after geo nodes
        (post.take l.individual_after.val) (post.drop l.individual_after.val) st₃ l afterStart
        digests loc e o₁ v₃ i₃ le tail'
        (fun q hq => low q (by simp [List.mem_of_mem_take hq]))
        hAfter (by omega) (by rw [List.length_take]; omega)
        (by rw [List.length_take]; omega) inside
        (by rw [v₃v, List.length_append, List.length_take]; simp; omega)
        (by
          have : span (post.take l.individual_after.val) ≤ span post := by
            conv => rhs; rw [splitPost]
            rw [span_append]; omega
          omega)
      have suffix := list_suffix geo nodes (post.drop l.individual_after.val) st₄ l digests loc e
        o₁ v₄ i₄ ls₄ yields₄ (fun q hq => low q (by simp [List.mem_of_mem_drop hq]))
        (by rw [i₄v, List.length_take]; omega) (by rw [i₄v, List.length_take, List.length_drop]; omega)
        (by
          have : span (post.take l.individual_after.val) + span (post.drop l.individual_after.val)
              = span post := by rw [← span_append, List.take_append_drop]
          omega)
      simp [hv₃, run₄, suffix]
      apply vec_ext
      rw [items_vecOf, v₄v, v₃v, v₂items]
      have off : afterStart.val + (i₃.val - l.before.val - l.overlapping.val) = afterStart.val := by
        omega
      rw [off]
      simp only [List.append_assoc, List.singleton_append]
      have tl : (post.take l.individual_after.val).length = l.individual_after.val := by
        rw [List.length_take]; omega
      rw [tl]
    | Err err =>
      simp
      congr 1
      funext x
      congr 2
      have same : v₂ = vecOf (items v ++
          (digests.val.drop prefixStart.val).take (l.before.val - l.fold.val)) (by
            simp only [List.length_append, List.length_take, List.length_drop]; scalar_tac) :=
        vec_ext (by rw [items_vecOf]; exact v₂items)
      rw [same]

end List

/-! ## A proof of one location -/

/-- Peaks before the range that fold into the prefix accumulator. -/
def foldOf (backward : Bool) (inactive before : Nat) : Nat :=
  if backward then min inactive before else before

/-- Peaks after the range that the proof lists individually. -/
def individualOf (backward : Bool) (inactive before after : Nat) : Nat :=
  if backward then min (inactive - (before + 1)) after else after

/-- Index of the first individually listed peak after the range. -/
def afterStartOf (backward : Bool) (inactive before : Nat) : Nat :=
  (if foldOf backward inactive before = 0 then 0 else 1) + (before - foldOf backward inactive before)

/-- Index of the first path sibling. -/
def siblingsStartOf (backward : Bool) (inactive before after : Nat) : Nat :=
  afterStartOf backward inactive before + individualOf backward inactive before after +
    (if individualOf backward inactive before after < after then 1 else 0)

/-- Inactive peaks still to fold once the prefix accumulator replaces the folded ones. -/
def toFoldOf (backward : Bool) (inactive before : Nat) : Nat :=
  if foldOf backward inactive before = 0 then inactive
  else inactive - foldOf backward inactive before + 1

/-- The peak digests a reconstruction bags: the listed ones before the range, the rebuilt peak,
then the listed ones and the suffix accumulator after it. -/
def listed (digests : List Bytes) (afterStart siblingsStart : Nat) (peak : Bytes) : List Bytes :=
  digests.take afterStart ++ peak :: (digests.drop afterStart).take (siblingsStart - afterStart)

/-- The root over a bag of peak digests, or `none` if fewer than `toFold` are listed. -/
def bagRoot (domain : Aeneas.Std.Array Std.U8 2#usize) (backward : Bool) (leaves : Std.U64)
    (inactive : Std.U64) (toFold : Nat) : List Bytes → Option Bytes
  | [] => none
  | first :: rest => if toFold ≤ rest.length + 1 then
      some (rootTerm domain leaves inactive (bagWith foldTerm backward (toFold - 1) first rest))
    else none

/-- The result of a reconstruction once the traversal of the peak holding the range has
returned `r` and left the opening `o`. -/
def outcome {N : Type} (domain : Aeneas.Std.Array Std.U8 2#usize) (backward : Bool)
    (leaves : Std.U64) (inactive : Std.Usize) (pre post : Nat) (digests : List Bytes)
    (r : CoreModels.core.result.Result Bytes traversal.Error)
    (o : traversal.Opening N reconstruct.Single Unit Bytes) :
    CoreModels.core.result.Result Bytes reconstruct.Error :=
  match r with
  | .Err .MissingElements => .Err .MissingElements
  | .Err .MissingDigests => .Err .MissingDigests
  | .Ok peak =>
    match o.elements with
    | .Some _ => .Err .ExtraDigests
    | .None =>
      if o.cursor.val ≠ digests.length then .Err .ExtraDigests
      else
        match bagRoot domain backward leaves (UScalar.cast .U64 inactive)
            (toFoldOf backward inactive.val pre)
            (listed digests (afterStartOf backward inactive.val pre)
              (siblingsStartOf backward inactive.val pre post) peak) with
        | some root => .Ok root
        | none => .Err .InvalidProof

section Single
variable {G P N : Type} (geo : reconstruct.Geometry G P) (nodes : traversal.Nodes N Bytes)

/-- What the production reconstruction returns for a proof of one item at `loc`, held by the
peak `(pos, h)` with `pre` peaks before it and `post` after it. Unless the proof carries exactly
the digests its layout needs, it fails; otherwise it runs the traversal of that peak from the
first path sibling, and its result is the `outcome` of that traversal. -/
theorem reconstruct_single (g : G) (n : N) (domain : Aeneas.Std.Array Std.U8 2#usize)
    (backward : Bool) (leaves : Std.U64) (inactive : Std.Usize) (digests : Slice Bytes)
    (loc : Std.U64) (item : Slice Std.U8) (pre post : List (Std.U64 × Std.U32)) (pos : Std.U64)
    (h : Std.U32) (st : P) (maxLeaves : Std.U64)
    (hmax : geo.max_leaves g = RustM.ok maxLeaves) (bound : leaves.val ≤ maxLeaves.val)
    (small : maxLeaves.val < 2 ^ 63)
    (hpeaks : geo.peaks g leaves = RustM.ok st)
    (yields : Yields geo.PeaksInst.next st (pre ++ (pos, h) :: post))
    (low : Low (pre ++ (pos, h) :: post)) (total : span (pre ++ (pos, h) :: post) = leaves.val)
    (inside : span pre ≤ loc.val ∧ loc.val < span pre + 2 ^ h.val)
    (count : pre.length + 1 + post.length ≤ 64)
    (boundary : inactive.val ≤ pre.length + 1 + post.length) :
    ∃ (w ls e : Std.U64) (first : Std.Usize), w.val = 2 ^ h.val ∧ ls.val = span pre ∧
      e.val = loc.val + 1 ∧
      first.val = siblingsStartOf backward inactive.val pre.length post.length ∧
      reconstruct.reconstruct geo dyTerms nodes single element noCollect g () n domain backward
        leaves inactive digests loc 1#u64 (.Some item) () =
      if digests.val.length < first.val + h.val then RustM.ok (.Err .MissingDigests)
      else if first.val + h.val < digests.val.length then RustM.ok (.Err .ExtraDigests)
      else (do
        let (r, o) ← traversal.reconstruct (backend nodes)
          ⟨n, .Some item, digests, first, ()⟩ pos w ls loc e
        RustM.ok (outcome domain backward leaves inactive pre.length post.length digests.val r o))
      := by
  have one : 1 ≤ 2 ^ h.val := Nat.one_le_two_pow
  have whole := total
  rw [span_append, span_cons] at whole
  have hh : h.val ≤ 62 := low (pos, h) (by simp)
  obtain ⟨stop, hstop, stopv⟩ := add_ok loc 1#u64 (by scalar_tac)
  have stopv' : stop.val = loc.val + 1 := by simpa using stopv
  obtain ⟨b, a, sib, hloop, bv, av, sibv⟩ := classify_single geo pre post pos h st loc stop yields
    low stopv' inside (by omega) count
  obtain ⟨l, hl, lb, lo, la, lf, li⟩ := layout_some b a inactive backward (by omega)
    (by omega)
  have foldLe : l.fold.val ≤ l.before.val := by
    rw [lf, lb]; split <;> omega
  have indLe : l.individual_after.val ≤ l.after.val := by
    rw [li, la]; split <;> omega
  obtain ⟨fd, sd, ⟨aStart, hAfter, aStartv⟩, ⟨sStart, hSuffix, sStartv⟩,
    ⟨first, hFirst, firstv⟩⟩ := offsets_ok l (by rw [lb, la]; omega) foldLe indLe
  have lbv : l.before.val = pre.length := by rw [lb, bv]
  have lav : l.after.val = post.length := by rw [la, av]
  have firstSmall : first.val ≤ 130 := by rw [firstv]; split <;> split <;> omega
  obtain ⟨req, hreq, reqv⟩ := add_ok first sib (by scalar_tac)
  obtain ⟨w, hw, wv⟩ := width_ok h hh
  have lsFits : span pre < 2 ^ 64 := by omega
  let lsW : Std.U64 := ⟨BitVec.ofNat 64 (span pre)⟩
  have lsWv : lsW.val = span pre := by
    change (BitVec.ofNat 64 (span pre)).toNat = span pre
    simp; omega
  have firstEq : first.val = siblingsStartOf backward inactive.val pre.length post.length := by
    rw [firstv, lf, li, lb, la, bv, av]
    cases backward <;> simp [siblingsStartOf, afterStartOf, foldOf, individualOf]
  refine ⟨w, lsW, stop, first, wv, lsWv, stopv', firstEq, ?_⟩
  have nz : ¬ (1#u64 = 0#u64) := by decide
  have startOk : ¬ maxLeaves.val ≤ loc.val := by omega
  obtain ⟨room, hroom, roomv⟩ := sub_ok maxLeaves loc (by omega)
  have roomNz : ¬ room.val = 0 := by omega
  have countOk : ¬ room.val < (1#u64 : Std.U64).val := by simp; omega
  have endOk : ¬ leaves.val < stop.val := by omega
  have sizeOk : ¬ maxLeaves.val < leaves.val := by omega
  have reqh : req.val = first.val + h.val := by rw [reqv, sibv]
  unfold reconstruct.reconstruct
  simp [hmax, nz, startOk, hroom, countOk, hstop, endOk, sizeOk, hpeaks, hloop, hl, hFirst, hreq,
    roomNz, len_ok, reqh]
  by_cases short : digests.val.length < first.val + h.val
  · simp [short]
  by_cases long : first.val + h.val < digests.val.length
  · simp [short, long]
  simp only [short, long, ↓reduceIte]
  have exact : digests.val.length = first.val + h.val := by omega
  have aStartLe : aStart.val ≤ first.val := by rw [aStartv, firstv]; omega
  rw [vec_new_eq, fd]
  obtain ⟨v₁, v₁v, hv⟩ : ∃ v₁ : DigestVec,
      items v₁ = digests.val.take (if l.fold.val = 0 then 0 else 1) ∧
      (if (if l.fold.val = 0 then 0#usize else 1#usize) = 1#usize then do
          let t ← Slice.index_usize digests 0#usize
          CoreModels.alloc.vec.Vec.push (vecOf [] (by simp)) t
        else RustM.ok (vecOf [] (by simp))) = RustM.ok v₁ := by
    by_cases z : l.fold.val = 0
    · have ne : ¬ ((0#usize : Std.Usize) = 1#usize) := by decide
      exact ⟨vecOf [] (by simp), by simp [items_vecOf, z], by simp [z, ne]⟩
    · have nonempty : 0 < digests.val.length := by
        rw [aStartv] at aStartLe; simp [z] at aStartLe; omega
      obtain ⟨v₁, hp, pv⟩ := push_ok (vecOf [] (by simp)) (digests.val[0]'nonempty)
        (by simp [items_vecOf])
      refine ⟨v₁, ?_, ?_⟩
      · rw [pv, items_vecOf]; simp [z]
        rw [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem nonempty]
        rfl
      · simp only [z, ↓reduceIte, index_ok digests 0#usize (by simpa using nonempty),
          Std.bind_tc_ok, Std.bind_ok]
        exact hp
  simp only [Std.bind_tc_ok, Std.bind_ok]
  rw [hv]
  simp only [Std.bind_tc_ok, Std.bind_ok]
  have psv : (if l.fold.val = 0 then 0#usize else 1#usize).val =
      if l.fold.val = 0 then 0 else 1 := by split <;> simp
  have lov : l.overlapping.val = 1 := by simp [lo]
  have hPrefix : reconstruct.Layout.prefix_start l =
      RustM.ok (if l.fold.val = 0 then 0#usize else 1#usize) := by
    simp [reconstruct.Layout.prefix_start, fd]
  obtain ⟨ls, lsv, run⟩ := list_single geo nodes pre post pos h st l digests loc stop w
    (if l.fold.val = 0 then 0#usize else 1#usize) aStart ⟨n, .Some item, digests, first, ()⟩ v₁
    yields low (by omega) count lbv lov lav foldLe indLe hPrefix hAfter (by rw [aStartv, psv])
    (by rw [firstv] at exact; rw [aStartv]; omega) hw wv (by rw [v₁v]; simp; split <;> omega)
  have lsEq : ls = lsW := UScalar.eq_of_val_eq (by rw [lsv, lsWv])
  subst lsEq
  have listEq : reconstruct.list_peaks geo nodes single element noCollect g l leaves digests loc
      stop ⟨n, .Some item, digests, first, ()⟩ v₁ =
      listLoop geo nodes st l digests loc stop ⟨n, .Some item, digests, first, ()⟩ v₁ 0#usize
        0#u64 := by
    simp [reconstruct.list_peaks, hpeaks]
  simp only [traversal.Opening.new, Std.bind_tc_ok, Std.bind_ok]
  rw [listEq, run]
  simp
  congr 1
  funext x
  obtain ⟨r, o₁⟩ := x
  cases r with
  | Err err =>
    cases err <;> simp [reconstruct.missing, outcome]
  | Ok d =>
    obtain ⟨k, hk, kv⟩ := inactive_after_fold_ok l inactive (by omega)
    have sStartLt : sStart.val ≤ first.val := by rw [sStartv, firstv]; omega
    simp
    generalize hV : (vecOf _ _ : DigestVec) = V
    have Vitems : items V = items v₁ ++ ((digests.val.drop
        (if l.fold.val = 0 then 0 else 1)).take (l.before.val - l.fold.val) ++
          d :: (digests.val.drop aStart.val).take l.individual_after.val) := by
      rw [← hV, items_vecOf, psv]
    rw [sd]
    have sfxv : ∀ c : Bool, ((if c then 1#usize else 0#usize) : Std.Usize).val =
        if c then 1 else 0 := by intro c; split <;> simp
    obtain ⟨W, hW, Witems⟩ : ∃ W : DigestVec,
        (if (if l.individual_after.val < l.after.val then 1#usize else 0#usize) = 1#usize then do
            let i4 ← reconstruct.Layout.suffix_start l
            let t ← Slice.index_usize digests i4
            CoreModels.alloc.vec.Vec.push V t
          else RustM.ok V) = RustM.ok W ∧
        items W = items V ++ (digests.val.drop sStart.val).take
          (if l.individual_after.val < l.after.val then 1 else 0) := by
      by_cases sfx : l.individual_after.val < l.after.val
      · have firstS : first.val = sStart.val + 1 := by
          rw [firstv, sStartv, if_pos sfx]
        have sIn : sStart.val < digests.val.length := by omega
        have vlen : (items V).length < 1000 := by
          rw [Vitems, v₁v]
          simp only [List.length_append, List.length_cons]
          have a1 := List.length_take_le (if l.fold.val = 0 then 0 else 1) digests.val
          have a2 := List.length_take_le (l.before.val - l.fold.val)
            (digests.val.drop (if l.fold.val = 0 then 0 else 1))
          have a3 := List.length_take_le l.individual_after.val (digests.val.drop aStart.val)
          have one : (if l.fold.val = 0 then 0 else 1) ≤ 1 := by split <;> omega
          omega
        obtain ⟨v₃, hp, pv⟩ := push_ok V (digests.val[sStart.val]'sIn) vlen
        refine ⟨v₃, by simp [sfx, hSuffix, index_ok digests sStart sIn, hp], ?_⟩
        rw [pv]
        simp [sfx, List.take_one, List.head?_drop, List.getElem?_eq_getElem sIn]
      · refine ⟨V, by simp [sfx], by simp [sfx]⟩
    simp only [Std.bind_ok, Std.bind_tc_ok]
    rw [hW]
    simp only [Std.bind_ok, Std.bind_tc_ok]
    -- The digests the reconstruction bags are the listed ones.
    have aStartEq : aStart.val = afterStartOf backward inactive.val pre.length := by
      rw [aStartv, lf, lbv, bv]; cases backward <;> simp [afterStartOf, foldOf]
    have Wlisted : items W = listed digests.val (afterStartOf backward inactive.val pre.length)
        (siblingsStartOf backward inactive.val pre.length post.length) d := by
      rw [← aStartEq, ← firstEq, Witems, Vitems, v₁v, listed]
      have ps : (if l.fold.val = 0 then 0 else 1) ≤ digests.val.length := by
        have := aStartLe
        rw [aStartv] at this
        by_cases z : l.fold.val = 0 <;> simp only [z, ↓reduceIte] at this ⊢ <;> omega
      have pre' : digests.val.take (if l.fold.val = 0 then 0 else 1) ++
          (digests.val.drop (if l.fold.val = 0 then 0 else 1)).take (l.before.val - l.fold.val) =
          digests.val.take aStart.val := by
        rw [aStartv, List.take_add]
      have post' : (digests.val.drop aStart.val).take l.individual_after.val ++
          (digests.val.drop sStart.val).take
            (if l.individual_after.val < l.after.val then 1 else 0) =
          (digests.val.drop aStart.val).take (first.val - aStart.val) := by
        have : first.val - aStart.val = l.individual_after.val +
            (if l.individual_after.val < l.after.val then 1 else 0) := by
          rw [firstv, aStartv]; omega
        rw [this, List.take_add, List.drop_drop, sStartv, aStartv]
      rw [← pre', ← post']
      simp only [List.append_assoc, List.cons_append]
    have kEq : k.val = toFoldOf backward inactive.val pre.length := by
      rw [kv, lf, bv]; cases backward <;> simp [toFoldOf, foldOf]
    cases hel : o₁.elements with
    | some x =>
      simp [traversal.Opening.exhausted,
        reconstruct.Single.Insts.CoreIterTraitsIteratorIteratorElement.next, hel, outcome,
        CoreModels.core.option.Option.is_none, CoreModels.core.option.Option.is_some]
    | none =>
      simp [traversal.Opening.exhausted,
        reconstruct.Single.Insts.CoreIterTraitsIteratorIteratorElement.next, hel, outcome,
        CoreModels.core.option.Option.is_none, CoreModels.core.option.Option.is_some,
        traversal.Opening.impl.cursor]
      by_cases cur : o₁.cursor.val = digests.val.length
      · simp only [cur, ↓reduceIte, not_true_eq_false]
        obtain ⟨S, hS, Sv⟩ := deref_eq W
        cases hWl : Slice.val S with
        | nil => rw [Sv, Wlisted] at hWl; simp [listed] at hWl
        | cons f rs =>
          obtain ⟨e', hb⟩ := bagged_root_eq domain backward leaves k
            (UScalar.cast UScalarTy.U64 inactive) S f rs hWl
          rw [hk, hS]
          simp only [Std.bind_ok, Std.bind_tc_ok, Std.lift]
          rw [ends_new_eq]
          simp only [Std.bind_ok, Std.bind_tc_ok]
          rw [hb]
          simp [bagRoot, ← Wlisted, ← Sv, hWl, kEq]
          by_cases c : toFoldOf backward inactive.val pre.length ≤ rs.length + 1 <;> simp [c]
      · simp [cur]

end Single

end
end Qmdb.Reconstruct
