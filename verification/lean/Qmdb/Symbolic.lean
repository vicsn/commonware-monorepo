module
public import Qmdb.Assumptions
public import Qmdb.Verifier

/-! The verifier theorems on DyLean terms. DyLean's concatenation keeps hash inputs apart under
any hash, so every event that the extracted client step accepts names the stored item or the
finder returns a collision. DyLean's hash constructor has no collisions, so with it the collision
branch of `Verifier.unique_or_collision` is impossible: accepted openings are unique and the
production verifier is binding. The client step's decisions follow. Checked by Lean. -/

namespace Qmdb.Symbolic
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-! ## Binding -/

/-- DyLean's concatenation keeps hash inputs of one kind apart, whatever the hash. -/
theorem unambiguous (hash : Bytes → Bytes) : Verifier.Unambiguous (hashing hash) where
  leaf _ _ _ same := part_bytes_inj (concat_inj same).2
  node _ _ _ _ _ same := concat_inj (concat_inj same).2
  root _ _ _ _ same := (concat_inj (concat_inj same).2).2

/-- Uniqueness of accepted openings under symbolic hashing: two openings that the production
verifier accepts at the same location under the same root carry the same item and the same
siblings. -/
theorem unique (h : Std.U32) (loc : Std.U64) (root : Bytes) (a b : Slice Std.U8)
    (wa wb : Slice Bytes) (ha : qmdb.verify dyTerms () h loc root a wa = RustM.ok true)
    (hb : qmdb.verify dyTerms () h loc root b wb = RustM.ok true) : a = b ∧ wa = wb := by
  rcases Verifier.unique_or_collision symbolic (unambiguous Hash.hash) h loc root a b wa wb ha
      hb with
    same | ⟨x, y, -, clash⟩
  · exact same
  · exact absurd clash (no_collision x y)

/-- Binding of the production verifier under symbolic hashing: two openings that it accepts at
the same location under the same root carry the same item. -/
theorem binding (h : Std.U32) (loc : Std.U64) (root : Bytes) (a b : Slice Std.U8)
    (wa wb : Slice Bytes) (ha : qmdb.verify dyTerms () h loc root a wa = RustM.ok true)
    (hb : qmdb.verify dyTerms () h loc root b wb = RustM.ok true) : a = b :=
  (unique h loc root a b wa wb ha hb).1

/-! ## The client -/

/-- Every event that the extracted client step accepts, under any hash, names the snapshot height
and an in-range location, and its item is the stored one or `Verifier.finder` returns a collision
between the accepted opening and the snapshot's. -/
theorem client_step_sound [Snapshot] (message : Bytes) (loc : Std.U64) (ws : Slice Bytes)
    (event : qmdb.Acceptance)
    (accepted : qmdb.client_step Snapshot.scheme.terms messages () Snapshot.root Snapshot.height
      message loc ws = RustM.ok (some event)) :
    event.height = Snapshot.height ∧ event.location.val < 2^event.height.val ∧
      (event.item = Snapshot.items event.location ∨
        ∃ x y, Verifier.finder Snapshot.scheme event.height event.location event.item
          (Snapshot.items event.location) ws (Snapshot.siblings event.location) = some (x, y) ∧
          x ≠ y ∧ Snapshot.hash x = Snapshot.hash y) := by
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
      have hv' : qmdb.verify Snapshot.scheme.terms () Snapshot.height loc Snapshot.root item ws =
          RustM.ok true := hv
      obtain ⟨-, inside, -⟩ := Verifier.verify_true Snapshot.scheme hv'
      exact ⟨rfl, inside, Verifier.binding_or_collision Snapshot.scheme
        (unambiguous Snapshot.hash) _ _ _ _ _ _ _ hv' (Snapshot.honest loc inside)⟩

/-! ## Client decisions -/

/-- The client step decides like the verifier on a message carrying `item`, under any hash. -/
theorem client_step_carrying (T : terms.Terms Unit Bytes) (root : Bytes) (h : Std.U32)
    (item : Slice Std.U8) (loc : Std.U64) (ws : Slice Bytes) :
    qmdb.client_step T messages () root h (carrying item) loc ws =
      (do
        let b ← qmdb.verify T () h loc root item ws
        if b then RustM.ok (some { height := h, location := loc, item }) else RustM.ok none) := by
  unfold qmdb.client_step
  rw [parse_carrying]
  simp only [bind_ok]

/-- The extracted client logs the honest acceptance for every honest opening. -/
theorem honest_accepted (items : Std.U64 → Slice Std.U8) (h : Std.U32) (bound : h.val ≤ 62)
    (loc : Std.U64) (inside : loc.val < 2^h.val) :
    qmdb.client_step dyTerms messages () (Verifier.honestRoot symbolic items h.val) h
      (carrying (items loc)) loc (Verifier.honestSiblings symbolic items h.val loc bound) =
      RustM.ok (some { height := h, location := loc, item := items loc }) := by
  rw [client_step_carrying, Verifier.honest_opening symbolic items h bound loc inside]
  simp

/-- The extracted client rejects every other item at an honest snapshot's location, whatever
the siblings. -/
theorem substitution_rejected (items : Std.U64 → Slice Std.U8) (h : Std.U32) (bound : h.val ≤ 62)
    (loc : Std.U64) (inside : loc.val < 2^h.val) (item : Slice Std.U8) (other : item ≠ items loc)
    (ws : Slice Bytes) :
    qmdb.client_step dyTerms messages () (Verifier.honestRoot symbolic items h.val) h
      (carrying item) loc ws = RustM.ok none := by
  obtain ⟨b, hb⟩ :=
    Verifier.verify_total symbolic h loc (Verifier.honestRoot symbolic items h.val) item ws
  rw [client_step_carrying, hb]
  cases b with
  | false => simp
  | true =>
    exact absurd
      (binding _ _ _ _ _ _ _ hb (Verifier.honest_opening symbolic items h bound loc inside)) other

end
end Qmdb.Symbolic
