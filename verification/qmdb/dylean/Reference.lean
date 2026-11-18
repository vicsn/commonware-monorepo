module
public import DyTerms
public import Binding

/-! The handwritten client semantics that this experiment trusted before the specification moved
to Rust. It is now an untrusted, executable reference: `Correspondence` proves the extracted Rust
equal to it, and `SanityChecks` runs it. -/

namespace Qmdb.Reference
open DY Aeneas Aeneas.Std
@[expose] public section

/-- Accept `item` at `loc` under `root` if the opening rebuilds the root and is fully used. -/
def check (h loc : Nat) (root : Bytes) (item : ByteArray) (ws : List Bytes) : Bool :=
  h ≤ 63 && loc < 2^h &&
    match replay item h (2*(2^h-1)) 0 loc ws with
    | some (peak,[]) => decide (wrap h peak = root)
    | _ => false

theorem check_spec (h loc : Nat) (root : Bytes) (item : ByteArray) (ws : List Bytes) :
    check h loc root item ws = true ↔ accepts h loc root item ws := by
  unfold check accepts
  cases hr : replay item h (2*(2^h-1)) 0 loc ws with
  | none => simp
  | some pair => obtain ⟨p,rest⟩ := pair; cases rest <;> simp [and_assoc]

abbrev Acceptance := qmdb_dylean.client.Acceptance ByteArray

/-- The honest root of the snapshot. -/
def root [Snapshot] : Bytes :=
  let h := (Snapshot.height).val
  wrap h (tree Snapshot.items h (2*(2^h-1)) 0)

/-- The client's decision on a received message. -/
def step [Snapshot] (message : Bytes) (loc : Std.U64) (ws : Slice Bytes) : Option Acceptance :=
  match Literal.bytesToLiteral message with
  | none => none
  | some item =>
    if check (Snapshot.height).val loc.val root item ws.val
    then some { height := Snapshot.height, location := loc, item }
    else none

/-- Every accepted event names the snapshot height, an in-range location and the stored item. -/
theorem step_sound [Snapshot] (message : Bytes) (loc : Std.U64) (ws : Slice Bytes)
    (event : Acceptance) (accepted : step message loc ws = some event) :
    event.height = Snapshot.height ∧ event.location.val < 2^event.height.val ∧
      event.item = Snapshot.items event.location.val := by
  unfold step at accepted
  split at accepted
  · simp at accepted
  · split at accepted
    · rename_i checked
      cases accepted
      have valid := (check_spec ..).mp checked
      exact ⟨rfl, valid.2.1, inclusion_sound _ _ _ _ _ valid⟩
    · simp at accepted

end
end Qmdb.Reference
