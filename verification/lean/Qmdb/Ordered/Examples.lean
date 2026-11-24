module
import all DY.EquationalTheory.Hash
import Mathlib.Tactic.IntervalCases
public import Qmdb.Ordered.Extraction
public import Qmdb.Ordered.Database
public import Qmdb.Mmb.Raw

/-! Constructive examples of the empty database and a singleton after its first committed
update, laid out as production's MMB with its root domain bytes. -/

namespace Qmdb.Ordered.Examples
open DY Active Commonware.Symbolic
deriving instance DecidableEq for Mmb.Shape
deriving instance DecidableEq for Mmb.Plan

public section

private inductive Rows where
  | one (genesis : Bytes)
  | three (genesis update commit : Bytes)

private def Rows.n : Rows → Nat | .one _ => 1 | .three .. => 3
private def Rows.row : Rows → Nat → Bytes
  | .one g, _ => g
  | .three g u c, n => if n = 0 then g else if n = 1 then u else c

private def Rows.bitmap (r : Rows) : Chunk :=
  (Vector.replicate 32 0).set 0 (match r with | .one _ => 1 | .three .. => 6)

private theorem first_bit : activeBit ((Vector.replicate 32 0).set 0 1) 0 = true := by decide
private theorem next_bit : activeBit ((Vector.replicate 32 0).set 0 6) 1 = true := by decide

private def hash (term : Bytes) : Mmb.Digest :=
  ⟨Hash.hash term, by simp [Hash.hashLength]⟩

private def leaf (position : UInt64) (item : Bytes) : Mmb.Digest :=
  hash (Concat.concat (Mmb.count position) item)

private def Rows.bag : Rows → Mmb.Digest
  | .one g => leaf 0 g
  | .three g u c =>
    let node := hash (Concat.concat (Mmb.count 2) (Concat.concat (leaf 0 g).val (leaf 1 u).val))
    hash (Concat.concat node.val (leaf 3 c).val)

private def Rows.header (r : Rows) : Mmb.Header :=
  let n := UInt64.ofNat r.n
  ⟨n, 0, fun _ => rfl, r.bag, hash (Concat.concat (Mmb.count n) r.bag.val),
    none, some (n, hash (literal r.bitmap))⟩

private def Rows.opPath : Rows → Nat → List Step
  | .one _, _ => [.hash, .right, .left, .hash, .right, .right, .hash, .right]
  | .three .., n =>
    [.hash, .right, .left, .hash, .right, .right, .hash] ++
      (if n = 0 then [.left, .hash, .right, .left]
       else if n = 1 then [.left, .hash, .right, .right] else [.right]) ++ [.hash, .right]

private def bitPath : List Step := [.hash, .right, .right, .right, .hash]

private theorem open_hash {p : List Step} {t x : Bytes} (h : Opens p t x) :
    Opens (.hash :: p) (Hash.hash t) x := by
  obtain ⟨w, eq, rfl⟩ := h
  exact ⟨.hash w, congrArg (Step.hash :: ·) eq, rfl⟩

private theorem open_left {p : List Step} {t x : Bytes} (r : Bytes) (h : Opens p t x) :
    Opens (.left :: p) (Concat.concat t r) x := by
  obtain ⟨w, eq, rfl⟩ := h
  exact ⟨.left w r, congrArg (Step.left :: ·) eq, rfl⟩

private theorem open_right {p : List Step} {t x : Bytes} (l : Bytes) (h : Opens p t x) :
    Opens (.right :: p) (Concat.concat l t) x := by
  obtain ⟨w, eq, rfl⟩ := h
  exact ⟨.right l w, congrArg (Step.right :: ·) eq, rfl⟩

local macro "open_fields" : tactic => `(tactic|
  ((repeat' first | apply open_hash | apply open_left | apply open_right);
   exact ⟨.tip, rfl, rfl⟩))

private def Rows.snapshot (r : Rows) : Active.Snapshot where
  root := r.header.root
  leaves := r.n
  item := r.row
  chunk := fun _ => r.bitmap
  itemPath := r.opPath
  chunkPath := fun _ => some bitPath
  itemOpening := by
    intro i hi
    cases r with
    | one g => have : i = 0 := by simpa [Rows.n] using hi
               subst i
               open_fields
    | three g u c =>
      change i < 3 at hi
      interval_cases i <;> open_fields
  chunkOpening := by
    intro i p h
    obtain rfl := Option.some.inj h
    cases r <;> open_fields
  liveCovered := by intros; rfl

private theorem Rows.layout (r : Rows) : Mmb.Layout r.snapshot 0 where
  pathsAt := by
    intro i hi
    cases r with
    | one g =>
      change i < 1 at hi
      interval_cases i
      dsimp only [Rows.snapshot, Rows.n, Rows.opPath, Rows.bitmap, bitPath]
      decide
    | three g u c =>
      change i < 3 at hi
      interval_cases i <;> dsimp only [Rows.snapshot, Rows.n, Rows.opPath, Rows.bitmap, bitPath] <;>
        decide
  zeroPosition := by
    intro loc item bm inside zero
    cases r <;> simp [Rows.snapshot, Rows.n, Mmb.graftedChunks] at zero

private def emptyDb [LinearOrder K] (enc : Encoding K V) : Snapshot K V enc where
  auth := (Rows.one (enc (.commit none 0))).snapshot
  entry := fun _ => .commit none 0
  encoded := by intros; rfl
  activeUpdate := by intros; contradiction
  adjacent := by intros; contradiction
  commitBounds := by
    intro i m f hi eq _
    change i < 1 at hi
    cases eq
    exact ⟨by change i + 1 = 1; omega, fun _ _ _ => Nat.zero_le _⟩

private def oneRow (key : K) (v : V) (i : Nat) : Operation K V :=
  if i = 0 then .commit none 0 else if i = 1 then .update key v key else .commit none 1

private def oneDb [LinearOrder K] (enc : Encoding K V) (key : K) (v : V) : Snapshot K V enc where
  auth := (Rows.three (enc (.commit none 0)) (enc (.update key v key))
    (enc (.commit none 1))).snapshot
  entry := oneRow key v
  encoded := by
    intro i hi
    change i < 3 at hi
    interval_cases i <;> rfl
  activeUpdate := by
    intro i k w next hi eq
    change i < 3 at hi
    interval_cases i <;> simp [oneRow] at eq
    obtain ⟨rfl, rfl, rfl⟩ := eq
    constructor
    · intro _ j a b
      change j < 3 at b
      have : j = 2 := by omega
      subst j
      rfl
    · intro _
      change activeBit ((Vector.replicate 32 0).set 0 6) 1 = true
      decide
  adjacent := by
    intro i k w next j q x stop hi eq _ hj other _ gap
    change i < 3 at hi
    change j < 3 at hj
    interval_cases i <;> interval_cases j <;> simp [oneRow] at eq other
    obtain ⟨rfl, rfl, rfl⟩ := eq
    obtain ⟨rfl, rfl, rfl⟩ := other
    simp [Between] at gap
  commitBounds := by
    intro i m f hi eq bit
    change i < 3 at hi
    interval_cases i <;> simp [oneRow] at eq
    · have dead : activeBit ((Vector.replicate 32 0).set 0 6) 0 = false := by decide
      change activeBit ((Vector.replicate 32 0).set 0 6) 0 = true at bit
      rw [dead] at bit
      contradiction
    · obtain ⟨rfl, rfl⟩ := eq
      refine ⟨rfl, fun j hj bj => ?_⟩
      change j < 3 at hj
      interval_cases j
      · have dead : activeBit ((Vector.replicate 32 0).set 0 6) 0 = false := by decide
        change activeBit ((Vector.replicate 32 0).set 0 6) 0 = true at bj
        rw [dead] at bj
        contradiction
      · decide
      · decide

private def Rows.index : Rows → Nat | .one _ => 0 | .three .. => 1

private def Rows.raw (r : Rows) : Mmb.RawProof :=
  let digests := match r with
    | .one _ => []
    | .three g _ c => [(leaf 3 c).val, (leaf 0 g).val]
  ⟨digests, r.header.ops.val, none, some (hash (literal r.bitmap)).val, r.bitmap⟩

private def Rows.recipe (r : Rows) : Mmb.Plan := Id.run do
  let single : Mmb.Shape := .hash (.pair (.atom (.word r.index)) (.atom .item))
  let bagged : Mmb.Shape := match r with
    | .one _ => single
    | .three .. =>
      let node : Mmb.Shape := .hash (.pair (.atom (.word 2)) (.pair (.atom (.sibling 1)) single))
      .hash (.pair node (.atom (.sibling 0)))
  let merkle : Mmb.Shape := .hash (.pair (.atom .domain) (.pair (.atom (.word r.n)) bagged))
  let suffix : Mmb.Shape := .pair (.atom (.word r.n)) (.hash (.atom .bitmap))
  return ⟨(match r with | .one _ => 0 | .three .. => 2),
    .hash (.pair (.atom .ops) (.pair merkle suffix))⟩


private theorem Rows.route (r : Rows) :
    Mmb.plan r.n 0 r.index true = some r.recipe := by
  cases r <;> dsimp only [Rows.n, Rows.index, Rows.recipe] <;> decide

private theorem Rows.raw_valid (r : Rows) :
    r.raw.fieldsValid r.recipe r.n r.index = true := by
  cases r <;> simp [Mmb.RawProof.fieldsValid, Rows.raw, Rows.recipe, Rows.index, Rows.n,
    Mmb.Shape.available, Rows.header, Rows.bitmap, Mmb.suffixMatches, Mmb.graftedChunks,
    hash, Hash.hashLength, leaf, first_bit, next_bit]

private theorem Rows.raw_verify (r : Rows) :
    r.raw.verify r.header.root r.n 0 r.index (r.row r.index) = true := by
  simp [Mmb.RawProof.verify, Mmb.RawProof.reconstruct, r.route, r.raw_valid]
  cases r <;> rfl

/-- A concrete one-commit genesis snapshot. -/
def empty [LinearOrder K] (enc : Encoding K V) : Database enc :=
  let r := Rows.one (enc (.commit none 0))
  ⟨emptyDb enc, r.header, rfl, rfl, r.layout⟩

/-- All keys have accepted raw exclusion proofs against the genesis snapshot. -/
theorem empty_claim [LinearOrder K] (enc : Encoding K V) (key : K) :
    ∃ p : Proof K V Mmb.RawProof, Extraction.Accepts enc
      (fun l op t => t.verify (empty enc).header.root (empty enc).header.leaves.toNat
        (empty enc).header.inactive.toNat l op = true) key none p := by
  let r := Rows.one (enc (.commit none 0))
  exact ⟨.empty 0 none r.raw, Extraction.accepts_iff.mpr r.raw_verify⟩

/-- A concrete three-leaf genesis, update, and commit journal with a single live key. -/
def singleton [LinearOrder K] (enc : Encoding K V) (key : K) (v : V) : Database enc :=
  let r := Rows.three (enc (.commit none 0)) (enc (.update key v key)) (enc (.commit none 1))
  ⟨oneDb enc key v, r.header, rfl, rfl, r.layout⟩

/-- One compressed update opening proves membership and every honest singleton-gap exclusion. -/
theorem singleton_claims [LinearOrder K] (enc : Encoding K V) (key other : K) (v : V)
    (distinct : key ≠ other) :
    let h := (singleton enc key v).header
    let check := fun loc item (p : Mmb.RawProof) =>
      p.verify h.root h.leaves.toNat h.inactive.toNat loc item = true
    ∃ p q, Extraction.Accepts enc check key (some v) p ∧
      Extraction.Accepts enc check other none q := by
  let r := Rows.three (enc (.commit none 0)) (enc (.update key v key)) (enc (.commit none 1))
  exact ⟨.member 1 key r.raw, .gap 1 key v key r.raw, Extraction.accepts_iff.mpr r.raw_verify,
    Extraction.accepts_iff.mpr ⟨(singleton_gap key other).mpr distinct, r.raw_verify⟩⟩

end
end Qmdb.Ordered.Examples
