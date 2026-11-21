module
public import Leaf.Assumptions
public import Commonware.Symbolic.RustM

/-! The extracted leaf client under symbolic hashing. The production leaf digest of an item is the
hash of its position and the item, DyLean's hash has no collisions, and so the client step accepts
exactly the committed item. Checked by Lean. -/

namespace Leaf.Step
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-- The big-endian bytes of a position, as a term. -/
def position (p : Std.U64) : Bytes :=
  part (.Bytes (Aeneas.Std.core.num.U64.to_be_bytes p).to_slice)

/-- The production leaf digest as a term: the hash of the position and the item. -/
theorem leaf_digest_eq (p : Std.U64) (item : Slice Std.U8) :
    terms.leaf_digest dyTerms () p item =
      RustM.ok (Hash.hash (Concat.concat (position p) (part (.Bytes item)))) := by
  simp [terms.leaf_digest, hashing, CoreModels.core.num.U64.to_be_bytes,
    rust_primitives.arithmetic.to_be_bytes_u64, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, Scheme.terms, symbolic, chain, position]

/-- Two items with one leaf digest at one position are the same item. -/
theorem leaf_digest_inj {p : Std.U64} {a b : Slice Std.U8} {d : Bytes}
    (ha : terms.leaf_digest dyTerms () p a = RustM.ok d)
    (hb : terms.leaf_digest dyTerms () p b = RustM.ok d) : a = b := by
  rw [leaf_digest_eq] at ha hb
  have same := (ok_inj ha).trans (ok_inj hb).symm
  exact part_bytes_inj (concat_inj (Hash.hash_inj _ _ same)).2

/-- The client step decides by comparing the leaf digest of the parsed item with the commitment. -/
theorem client_step_carrying (commitment : Bytes) (item : Slice Std.U8) :
    leaf.client_step dyTerms messages () commitment (carrying item) =
      (do
        let digest ← terms.leaf_digest dyTerms () leaf.POSITION item
        if digest = commitment then RustM.ok (some { item }) else RustM.ok none) := by
  unfold leaf.client_step
  rw [parse_carrying]
  simp [Scheme.terms]

/-- Every event that the extracted client step accepts carries the committed item. -/
theorem client_step_sound [Commitment] (message : Bytes) (event : leaf.Acceptance)
    (accepted : leaf.client_step dyTerms messages () Commitment.digest message =
      RustM.ok (some event)) : event.item = Commitment.item := by
  unfold leaf.client_step at accepted
  obtain ⟨parsed, -, k⟩ := bind_eq_ok accepted
  cases parsed with
  | none => simp at k
  | some item =>
    obtain ⟨digest, computed, k'⟩ := bind_eq_ok k
    obtain ⟨verdict, compared, k''⟩ := bind_eq_ok k'
    have decided : decide (digest = Commitment.digest) = verdict := ok_inj compared
    cases verdict with
    | false => simp at k''
    | true =>
      have same := ok_inj k''
      simp at same
      subst same
      have equal : digest = Commitment.digest := by simpa using decided
      exact leaf_digest_inj (equal ▸ computed) Commitment.honest

/-- The extracted client accepts a message that carries the committed item. -/
theorem committed_accepted [Commitment] :
    leaf.client_step dyTerms messages () Commitment.digest (carrying Commitment.item) =
      RustM.ok (some { item := Commitment.item }) := by
  rw [client_step_carrying, Commitment.honest]
  simp

/-- The extracted client rejects a message that carries any other item. -/
theorem other_rejected [Commitment] (item : Slice Std.U8) (other : item ≠ Commitment.item) :
    leaf.client_step dyTerms messages () Commitment.digest (carrying item) = RustM.ok none := by
  rw [client_step_carrying, leaf_digest_eq]
  have differ : Hash.hash (Concat.concat (position leaf.POSITION) (part (.Bytes item))) ≠
      Commitment.digest := by
    intro same
    exact other (leaf_digest_inj ((leaf_digest_eq _ _).trans (congrArg RustM.ok same))
      Commitment.honest)
  simp [differ]

/-- Every item has a commitment. -/
theorem commitment_exists (item : Slice Std.U8) :
    ∃ digest : Bytes, terms.leaf_digest dyTerms () leaf.POSITION item = RustM.ok digest :=
  ⟨_, leaf_digest_eq _ _⟩

end
end Leaf.Step
