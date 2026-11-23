module
public import Qmdb.Ordered

/-! Reading the extracted ordered operation selectors with key comparison, identity clones,
and the proof payload passed unchanged to the active operation verifier. -/

namespace Qmdb.Ordered.Extraction
open Aeneas CoreModels commonware_symbolic DY
open Aeneas.Std hiding namespace core alloc
@[expose] public section

/-- Immutable values are read identically after a Rust clone. -/
def cloning : core.clone.Clone T := ⟨RustM.ok, fun _ x => RustM.ok x⟩

/-- Key ordering is the total order also used by the committed successor links. -/
def keys [LinearOrder K] : ordered.Key K :=
  ⟨cloning, ⟨fun a b => RustM.ok (decide (a = b)), fun a b => RustM.ok (decide (a ≠ b))⟩,
    fun a b => RustM.ok (decide (a < b))⟩

/-- A location is copied by value. -/
def locations : ordered.Graftable Nat := ⟨⟨cloning⟩⟩

/-- Extracted values have the application-selected payload type. -/
def values : ordered.ValueEncoding Unit V := ⟨cloning⟩

/-- The proof's digest fields are opaque to the ordered operation selectors. -/
def digest : ordered.Digest Unit := ⟨⟩

/-- Pass optional metadata to the extracted commit operation. -/
def metadata : Option V → core.option.Option V
  | none => .None
  | some v => .Some v

/-- Read the selected Rust operation back as a logical journal entry. -/
def readOp : ordered.Operation Nat K Unit V → Operation K V
  | .Update u => .update u.key u.value u.next_key
  | .Commit m l => .commit (match m with | .None => none | .Some v => some v) (UInt64.ofNat l)

/-- Run the production exclusion selector and retain the exact location and proof it selects. -/
def selectExclusion [LinearOrder K] (key : K)
    (p : ordered.ExclusionProof Nat K Unit Unit P V) :
    RustM (Option (Nat × Operation K V × P)) := do
  let result ← ordered.claim.exclusion locations keys values digest key p
  match result with
  | .None => RustM.ok none
  | .Some (proof, op) => RustM.ok (some (proof.loc, readOp op, proof.payload.2))

/-- Run the extracted selection method for the claimed proof kind. -/
def select [LinearOrder K] (key : K) : Option V → Proof K V P →
    RustM (Option (Nat × Operation K V × P))
  | some value, .member loc next p => do
    let op ← ordered.claim.membership locations keys values key value next
    RustM.ok (some (loc, readOp op, p))
  | none, .gap loc start value stop p =>
    selectExclusion key (.KeyValue ⟨loc, (), p⟩ ⟨start, value, stop⟩)
  | none, .empty loc m p =>
    selectExclusion key (.Commit ⟨loc.toNat, (), p⟩ (metadata m))
  | _, _ => RustM.ok none

/-- The verifier authenticates the operation and opening returned by the extracted selector. -/
def Accepts [LinearOrder K] (enc : Encoding K V) (openOp : Nat → Bytes → P → Prop)
    (key : K) (value : Option V) (p : Proof K V P) : Prop :=
  ∃ loc op proof, select key value p = RustM.ok (some (loc, op, proof)) ∧ openOp loc (enc op) proof

private theorem select_gap [LinearOrder K] (key start stop : K) (value : V) (p : P) (l : Nat) :
    select key none (.gap l start value stop p) =
      RustM.ok (if inGap start stop key then some (l, .update start value stop, p) else none) := by
  by_cases a : start = key <;> by_cases b : start < stop <;> by_cases c : key < start <;>
    by_cases d : key < stop <;>
    simp [select, selectExclusion, ordered.claim.exclusion, ordered.contains_cyclic,
      cyclic.contains, ordered.Update.Insts.CoreCloneClone.clone, keys, values,
      cloning, readOp, inGap, a, b, c, d, ← not_lt]

private theorem select_empty [LinearOrder K] (key : K) (l : UInt64) (m : Option V) (p : P) :
    select key none (.empty l m p) = RustM.ok (some (l.toNat, .commit m l, p)) := by
  cases m <;> simp [select, selectExclusion, ordered.claim.exclusion,
    core.option.Option.Insts.CoreCloneClone.clone, values, metadata, cloning, readOp]

/-- The extracted selectors accept exactly the ordered verifier's three valid claim forms. -/
theorem accepts_iff [LinearOrder K] {enc : Encoding K V} {openOp : Nat → Bytes → P → Prop}
    {key : K} {v : Option V} {p : Proof K V P} :
    Accepts enc openOp key v p ↔ VerifyWith enc openOp key v p := by
  cases v with
  | some value =>
    cases p <;> simp [Accepts, VerifyWith, select, ordered.claim.membership, keys, cloning, readOp]
  | none =>
    cases p with
    | member => simp [Accepts, VerifyWith, select]
    | empty => simp [Accepts, VerifyWith, select_empty]
    | gap loc start value stop p =>
      cases h : inGap start stop key <;> simp [Accepts, VerifyWith, select_gap, h]

end
end Qmdb.Ordered.Extraction
