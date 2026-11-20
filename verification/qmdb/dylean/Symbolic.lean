module
public import DyTerms
public import Verifier

/-! The symbolic instance of the verifier theorems. DyLean's hash constructor has no collisions
and its concatenation keeps hash inputs apart, so the collision branch of
`Verifier.binding_or_collision` is impossible and the production verifier is binding. The client
step's decisions follow. Checked by Lean. -/

namespace Qmdb.Symbolic
open DY Aeneas Aeneas.Std CoreModels qmdb_dylean
@[expose] public section

/-! ## No collisions -/

theorem toByteArray_inj {a b : Slice Std.U8} (h : toByteArray a = toByteArray b) : a = b := by
  apply Slice.ext
  have lists : a.val.map (fun x => UInt8.ofNat x.val) = b.val.map (fun x => UInt8.ofNat x.val) := by
    have := congrArg ByteArray.data h
    simpa [toByteArray] using this
  refine List.map_injective_iff.mpr ?_ lists
  intro x y same
  apply UScalar.eq_of_val_eq
  have hx : x.val < 256 := by scalar_tac
  have hy : y.val < 256 := by scalar_tac
  have := congrArg UInt8.toNat same
  simp at this
  omega

theorem part_bytes_inj {a b : Slice Std.U8}
    (h : part (.Bytes a) = (part (.Bytes b) : Bytes)) : a = b := by
  apply toByteArray_inj
  simpa only [part, Literal.bytesToLiteral_literalToBytes, Option.some.injEq] using
    congrArg (Literal.bytesToLiteral (Bytes := Bytes)) h

theorem concat_inj {a b c d : Bytes} (h : Concat.concat a b = Concat.concat c d) :
    a = c ∧ b = d := by
  simp only [Concat.concat] at h
  grind

/-- DyLean's concatenation keeps hash inputs of one kind apart. -/
theorem unambiguous : symbolic.Unambiguous where
  leaf _ _ _ same := part_bytes_inj (concat_inj same).2
  node _ _ _ _ _ same := concat_inj (concat_inj same).2
  root _ _ _ _ same := (concat_inj (concat_inj same).2).2

/-- DyLean's hash constructor has no collisions. -/
theorem no_collision (x y : Bytes) : ¬ symbolic.Collision x y :=
  fun clash => clash.1 (Hash.hash_inj _ _ clash.2)

/-- Binding of the production verifier under symbolic hashing: two openings that it accepts at
the same location under the same root carry the same item. -/
theorem binding (h : Std.U32) (loc : Std.U64) (root : Bytes) (a b : Slice Std.U8)
    (wa wb : Slice Bytes) (ha : client.verify dyTerms () h loc root a wa = RustM.ok true)
    (hb : client.verify dyTerms () h loc root b wb = RustM.ok true) : a = b := by
  rcases Verifier.binding_or_collision symbolic unambiguous h loc root a b wa wb ha hb with
    same | ⟨x, y, -, clash⟩
  · exact same
  · exact absurd clash (no_collision x y)

/-! ## The client -/

/-- Every event that the extracted client step accepts names the snapshot height, an in-range
location and the stored item. -/
theorem client_step_sound [Snapshot] (message : Bytes) (loc : Std.U64) (ws : Slice Bytes)
    (event : client.Acceptance)
    (accepted : client.client_step messages () Snapshot.root Snapshot.height message loc ws =
      RustM.ok (some event)) :
    event.height = Snapshot.height ∧ event.location.val < 2^event.height.val ∧
      event.item = Snapshot.items event.location := by
  unfold client.client_step at accepted
  obtain ⟨parsed, -, k⟩ := Verifier.bind_eq_ok accepted
  cases parsed with
  | none => simp at k
  | some item =>
    obtain ⟨verdict, hv, k'⟩ := Verifier.bind_eq_ok k
    cases verdict with
    | false => simp at k'
    | true =>
      have same := Verifier.ok_inj k'
      simp at same
      subst same
      have hv' : client.verify dyTerms () Snapshot.height loc Snapshot.root item ws =
          RustM.ok true := hv
      obtain ⟨-, inside, -⟩ := Verifier.verify_true symbolic hv'
      obtain ⟨ws', honest⟩ := Snapshot.honest loc inside
      exact ⟨rfl, inside, binding _ _ _ _ _ _ _ hv' honest⟩

/-! ## Client decisions -/

/-- A message carrying `item` as a literal. -/
def carrying (item : Slice Std.U8) : Bytes := Literal.literalToBytes (toByteArray item)

theorem toSlice_toByteArray (s : Slice Std.U8) : toSlice (toByteArray s) = some s := by
  have fits := s.property
  have same : (s.val.map fun b => UInt8.ofNat b.val).map (fun x => (⟨x.toBitVec⟩ : Std.U8)) =
      s.val := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id s.val]
    apply List.map_congr_left
    intro b _
    apply UScalar.eq_of_val_eq
    change (BitVec.ofNat 8 b.val).toNat = b.val
    have : b.val < 2^8 := by scalar_tac
    simp
  have short : (toByteArray s).data.toList.length ≤ Usize.max := by simp [toByteArray]
  unfold toSlice
  simp only [short, ↓reduceDIte]
  congr 1
  apply Slice.ext
  simpa [Slice.from_val, toByteArray] using same

theorem parse_carrying (item : Slice Std.U8) :
    messages.parse () (carrying item) = RustM.ok (some item) := by
  simp [messages, carrying, Literal.bytesToLiteral_literalToBytes, toSlice_toByteArray]

/-- The client step decides like the verifier on a message carrying `item`. -/
theorem client_step_carrying (root : Bytes) (h : Std.U32) (item : Slice Std.U8) (loc : Std.U64)
    (ws : Slice Bytes) :
    client.client_step messages () root h (carrying item) loc ws =
      (do
        let b ← client.verify dyTerms () h loc root item ws
        if b then RustM.ok (some { height := h, location := loc, item }) else RustM.ok none) := by
  unfold client.client_step
  rw [parse_carrying]
  simp only [bind_ok]
  rfl

/-- The extracted client logs the honest acceptance for every honest opening. -/
theorem honest_accepted (items : Std.U64 → Slice Std.U8) (h : Std.U32) (bound : h.val ≤ 62)
    (loc : Std.U64) (inside : loc.val < 2^h.val) :
    client.client_step messages () (Verifier.honestRoot symbolic items h.val) h
      (carrying (items loc)) loc (Verifier.honestSiblings symbolic items h.val loc bound) =
      RustM.ok (some { height := h, location := loc, item := items loc }) := by
  rw [client_step_carrying, Verifier.honest_opening symbolic items h bound loc inside]
  simp

/-- The extracted client rejects every other item at an honest snapshot's location, whatever
the siblings. -/
theorem substitution_rejected (items : Std.U64 → Slice Std.U8) (h : Std.U32) (bound : h.val ≤ 62)
    (loc : Std.U64) (inside : loc.val < 2^h.val) (item : Slice Std.U8) (other : item ≠ items loc)
    (ws : Slice Bytes) :
    client.client_step messages () (Verifier.honestRoot symbolic items h.val) h (carrying item)
      loc ws = RustM.ok none := by
  obtain ⟨b, hb⟩ :=
    Verifier.verify_total symbolic h loc (Verifier.honestRoot symbolic items h.val) item ws
  rw [client_step_carrying, hb]
  cases b with
  | false => simp
  | true =>
    exact absurd
      (binding _ _ _ _ _ _ _ hb (Verifier.honest_opening symbolic items h bound loc inside)) other

#print axioms binding
#print axioms client_step_sound
#print axioms honest_accepted
#print axioms substitution_rejected

end
end Qmdb.Symbolic
