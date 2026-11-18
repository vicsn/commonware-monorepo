module
public import DyTerms
public import Binding

/-! An untrusted, executable reference for the client's decision, built on the handwritten model.
`Correspondence` proves the extracted Rust equal to it, and `Scenarios` runs it. -/

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

/-- The client's decision on a received message. -/
def step [Snapshot] (message : Bytes) (loc : Std.U64) (ws : Slice Bytes) : Option Acceptance :=
  match Literal.bytesToLiteral message with
  | none => none
  | some item =>
    if check (Snapshot.height).val loc.val Snapshot.root item ws.val
    then some { height := Snapshot.height, location := loc, item }
    else none

end
end Qmdb.Reference
