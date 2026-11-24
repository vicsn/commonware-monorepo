module
public import Qmdb.Inclusion

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
    (event : inclusion.Acceptance)
    (accepted :
      inclusion.accept_inclusion dyTerms messages () Snapshot.root Snapshot.height
        message loc ws = RustM.ok (some event)) :
    event.height = Snapshot.height ∧ event.location.val < 2 ^ event.height.val ∧
      event.item = Snapshot.items event.location := by
  unfold inclusion.accept_inclusion at accepted
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
      obtain ⟨-, inside⟩ := Inclusion.verify_bounds hv
      exact ⟨rfl, inside,
        (Inclusion.unique _ _ _ _ _ _ _ hv (Snapshot.honest loc inside)).1⟩

/-! ## Client decisions -/

/-- The client step decides like the verifier on a message carrying `item`. -/
theorem client_step_carrying (root : Bytes) (h : Std.U32) (item : Slice Std.U8) (loc : Std.U64)
    (ws : Slice Bytes) :
    inclusion.accept_inclusion dyTerms messages () root h (carrying item) loc ws =
      (do
        let b ← inclusion.verify_element_inclusion dyTerms () h loc root item ws
        if b then RustM.ok (some { height := h, location := loc, item }) else RustM.ok none) := by
  unfold inclusion.accept_inclusion
  rw [parse_carrying]
  simp only [bind_ok]

/-- The extracted client step returns the acceptance of the stored item at every location of the
snapshot, on the opening that the snapshot supplies. -/
theorem client_step_complete [Snapshot] (loc : Std.U64)
    (inside : loc.val < 2 ^ Snapshot.height.val) :
    inclusion.accept_inclusion dyTerms messages () Snapshot.root Snapshot.height
      (carrying (Snapshot.items loc)) loc (Snapshot.siblings loc) =
      RustM.ok (some
        { height := Snapshot.height, location := loc, item := Snapshot.items loc }) := by
  rw [client_step_carrying, Snapshot.honest loc inside]
  simp

/-- The extracted client step returns the honest acceptance for every honest opening. -/
theorem honest_accepted (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ Inclusion.maxHeight) (loc : Std.U64) (inside : loc.val < 2 ^ h.val) :
    inclusion.accept_inclusion dyTerms messages ()
      (Inclusion.honestRoot items h.val) h
      (carrying (items loc)) loc (Inclusion.honestSiblings items h.val loc bound) =
      RustM.ok (some { height := h, location := loc, item := items loc }) := by
  rw [client_step_carrying, Inclusion.honest_opening items h bound loc inside]
  simp

/-- The extracted client step rejects every other item at an honest snapshot's location,
whatever the siblings. -/
theorem substitution_rejected (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ Inclusion.maxHeight)
    (loc : Std.U64) (inside : loc.val < 2 ^ h.val) (item : Slice Std.U8) (other : item ≠ items loc)
    (ws : Slice Bytes) :
    inclusion.accept_inclusion dyTerms messages ()
      (Inclusion.honestRoot items h.val) h
      (carrying item) loc ws = RustM.ok none := by
  obtain ⟨b, hb⟩ := Inclusion.verify_total h loc (Inclusion.honestRoot items h.val) item ws
  rw [client_step_carrying, hb]
  cases b with
  | false => simp
  | true =>
    exact absurd
      (Inclusion.unique _ _ _ _ _ _ _ hb (Inclusion.honest_opening items h bound loc inside)).1
      other

end
end Qmdb.Symbolic
