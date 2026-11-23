module
public import Qmdb.Verifier

/-! The extracted client step on DyLean terms. Every event that it accepts names the snapshot
height, an in-range location and the item stored there: accepted openings are unique, and the
snapshot has an accepted opening for every stored item. The step's decisions on honest and on
substituted items follow. Checked by Lean. -/

namespace Qmdb.Symbolic
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-! ## The client -/

/-- Every event that the extracted client step accepts names the snapshot height, an in-range
location and the item stored there. -/
theorem client_step_sound [Snapshot] (message : Bytes) (loc : Std.U64) (ws : Slice Bytes)
    (event : qmdb.Acceptance)
    (accepted : qmdb.client_step dyTerms messages () Snapshot.root Snapshot.height message loc
      ws = RustM.ok (some event)) :
    event.height = Snapshot.height ∧ event.location.val < 2^event.height.val ∧
      event.item = Snapshot.items event.location := by
  unfold qmdb.client_step at accepted
  obtain ⟨parsed, -, k⟩ := bind_eq_ok accepted
  cases parsed with
  | none => simp at k
  | some item =>
    obtain ⟨verdict, hv, k'⟩ := bind_eq_ok k
    cases verdict with
    | false => simp at k'
    | true =>
      have same := ok_inj k'
      simp at same
      subst same
      obtain ⟨-, inside⟩ := Verifier.verify_bounds hv
      exact ⟨rfl, inside,
        (Verifier.unique _ _ _ _ _ _ _ hv (Snapshot.honest loc inside)).1⟩

/-! ## Client decisions -/

/-- The client step decides like the verifier on a message carrying `item`. -/
theorem client_step_carrying (root : Bytes) (h : Std.U32) (item : Slice Std.U8) (loc : Std.U64)
    (ws : Slice Bytes) :
    qmdb.client_step dyTerms messages () root h (carrying item) loc ws =
      (do
        let b ← qmdb.verify dyTerms () h loc root item ws
        if b then RustM.ok (some { height := h, location := loc, item }) else RustM.ok none) := by
  unfold qmdb.client_step
  rw [parse_carrying]
  simp only [bind_ok]

/-- The extracted client step returns the honest acceptance for every honest opening. -/
theorem honest_accepted (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ Verifier.maxHeight) (loc : Std.U64) (inside : loc.val < 2^h.val) :
    qmdb.client_step dyTerms messages () (Verifier.honestRoot items h.val) h
      (carrying (items loc)) loc (Verifier.honestSiblings items h.val loc bound) =
      RustM.ok (some { height := h, location := loc, item := items loc }) := by
  rw [client_step_carrying, Verifier.honest_opening items h bound loc inside]
  simp

/-- The extracted client step rejects every other item at an honest snapshot's location,
whatever the siblings. -/
theorem substitution_rejected (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ Verifier.maxHeight)
    (loc : Std.U64) (inside : loc.val < 2^h.val) (item : Slice Std.U8) (other : item ≠ items loc)
    (ws : Slice Bytes) :
    qmdb.client_step dyTerms messages () (Verifier.honestRoot items h.val) h
      (carrying item) loc ws = RustM.ok none := by
  obtain ⟨b, hb⟩ := Verifier.verify_total h loc (Verifier.honestRoot items h.val) item ws
  rw [client_step_carrying, hb]
  cases b with
  | false => simp
  | true =>
    exact absurd
      (Verifier.unique _ _ _ _ _ _ _ hb (Verifier.honest_opening items h bound loc inside)).1
      other

end
end Qmdb.Symbolic
