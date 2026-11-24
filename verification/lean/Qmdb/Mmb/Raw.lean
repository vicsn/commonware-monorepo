module
public import Qmdb.Mmb
public import Qmdb.MmbHeader
public import Qmdb.Mmb.Coverage

/-! Reconstruct a root from one compressed single-operation proof. The proof fields fill the
pinned MMB geometry. The two path witnesses are obtained by structural recursion on that
geometry; the final acceptance test compares the computed root to the trusted root. -/

namespace Qmdb.Mmb
open DY Commonware.Symbolic Active
@[expose] public section

/-- A transcript of local hash computations. Peer-supplied digests stay opaque. -/
inductive Expr where
  /-- A proof field or a locally encoded scalar. -/
  | atom (v : Bytes)
  /-- A local hash call. -/
  | hash (input : Expr)
  /-- Inputs concatenated for a local hash call. -/
  | pair (left right : Expr)

/-- Read the local computations in the ideal hash model. -/
def Expr.value : Expr → Bytes
  | .atom v => v
  | .hash e => Hash.hash e.value
  | .pair l r => Concat.concat l.value r.value

/-- Fill the hash-input program with the values from this proof. -/
def Shape.fill (get : Field → Bytes) : Shape → Expr
  | .atom f => .atom (get f)
  | .hash e => .hash (e.fill get)
  | .pair l r => .pair (l.fill get) (r.fill get)

/-- Every projected field has an opening under every substitution in the same program. -/
theorem Shape.opens (get : Field → Bytes) (f : Field) (e : Shape) {path : List Step}
    (hp : e.path f = some path) :
    Opens path (e.fill get).value (get f) := by
  induction e generalizing path with
  | atom v =>
    by_cases eq : v = f
    · simp [Shape.path, eq] at hp
      subst path
      exact ⟨.tip, rfl, by simp [Shape.fill, Expr.value, eq, Witness.rebuild]⟩
    · simp [Shape.path, eq] at hp
  | hash e ih =>
    cases h : e.path f with
    | none => simp [Shape.path, h] at hp
    | some inner =>
      obtain rfl : .hash :: inner = path := by simpa [Shape.path, h] using hp
      obtain ⟨w, wp, wr⟩ := ih h
      exact ⟨.hash w, by simp [Witness.path, wp], by simp [Witness.rebuild, wr, fill, Expr.value]⟩
  | pair l r il ir =>
    cases h : l.path f with
    | some inner =>
      obtain rfl : .left :: inner = path := by simpa [Shape.path, h, Option.or] using hp
      obtain ⟨w, wp, wr⟩ := il h
      exact ⟨.left w (r.fill get).value, by simp [Witness.path, wp],
        by simp [Witness.rebuild, wr, fill, Expr.value]⟩
    | none =>
      cases hr : r.path f with
      | none => simp [Shape.path, h, hr, Option.or] at hp
      | some inner =>
        obtain rfl : .right :: inner = path := by simpa [Shape.path, h, hr, Option.or] using hp
        obtain ⟨w, wp, wr⟩ := ir hr
        exact ⟨.right (l.fill get).value w, by simp [Witness.path, wp],
          by simp [Witness.rebuild, wr, fill, Expr.value]⟩

/-- The raw range-proof fields in addition to the location, dimensions and encoded operation. -/
structure RawProof where
  /-- Merkle digests in compressed prefix, suffix and DFS order. -/
  digests : List Bytes
  /-- Ops root carried by the range proof. -/
  opsRoot : Bytes
  /-- Digest of a complete chunk whose grafting ancestor has yet to be born. -/
  pending : Option Bytes
  /-- Digest of the trailing incomplete chunk. -/
  trailing : Option Bytes
  /-- Claimed bitmap chunk surrounding this location. -/
  chunk : Chunk

/-- Validate the presence, width, and, for a covered chunk, the supplied suffix digest. -/
def suffixMatches (present covered : Bool) (supplied : Option Bytes) (chunk : Bytes) : Bool :=
  match present, supplied with
  | false, none => true
  | true, some d => decide (d.length = 32) && (!covered || decide (Hash.hash chunk = d))
  | _, _ => false

/-- Read a field of the decoded proof. Shape references are checked before interpretation. -/
def RawProof.get (p : RawProof) (item : Bytes) : Field → Bytes
  | .domain => domainBytes
  | .word n => count (UInt64.ofNat n)
  | .item => item
  | .bitmap => literal p.chunk
  | .sibling i => p.digests[i]?.getD p.opsRoot
  | .ops => p.opsRoot
  | .pending => p.pending.getD p.opsRoot
  | .trailing => p.trailing.getD p.opsRoot

/-- Check that all peer-supplied digest references resolve. -/
def Shape.available (p : RawProof) : Shape → Bool
  | .atom (.sibling i) => i < p.digests.length
  | .atom .pending => p.pending.isSome
  | .atom .trailing => p.trailing.isSome
  | .atom _ => true
  | .hash e => e.available p
  | .pair l r => l.available p && r.available p

/-- Validity checks on the adversary's proof fields. -/
def RawProof.fieldsValid (p : RawProof) (recipe : Plan) (leaves loc : Nat) : Bool :=
  let complete := leaves / 256
  let grafted := graftedChunks leaves
  let idx := loc / 256
  let chunk := literal p.chunk
  activeBit p.chunk loc &&
    p.digests.length == recipe.count && p.opsRoot.length == 32 &&
    p.digests.all (fun d => d.length == 32) && recipe.tree.available p &&
    suffixMatches (grafted < complete) (idx = grafted) p.pending chunk &&
    suffixMatches (leaves % 256 ≠ 0) (idx = complete) p.trailing chunk

/-- Rebuild the root of a compressed proof by filling the routing program. -/
def RawProof.reconstruct (p : RawProof) (leaves inactive loc : Nat) (item : Bytes) :
    Option Expr := do
  let recipe ← plan leaves inactive loc true
  guard (p.fieldsValid recipe leaves loc)
  return recipe.tree.fill (p.get item)

/-- The public verifier accepts exactly when reconstruction returns the supplied root. -/
def RawProof.verify (p : RawProof) (root : Bytes) (leaves inactive loc : Nat)
    (item : Bytes) : Bool :=
  (p.reconstruct leaves inactive loc item).any (fun e => decide (e.value = root))

/-- Successful root reconstruction alone implies the two openings for any input fields. -/
theorem RawProof.sound {p : RawProof} {root : Bytes} {leaves inactive loc : Nat} {item : Bytes}
    (accepted : p.verify root leaves inactive loc item = true) :
    ∃ w, Mmb.Accepts root leaves inactive loc item w := by
  cases hplan : plan leaves inactive loc true with
  | none => simp [verify, reconstruct, hplan] at accepted
  | some recipe =>
    obtain ⟨hop, hbm⟩ := plan_coverage hplan
    obtain ⟨op, opFound⟩ := Option.isSome_iff_exists.mp hop
    obtain ⟨bm, bmFound⟩ := Option.isSome_iff_exists.mp hbm
    by_cases valid : p.fieldsValid recipe leaves loc = true
    · have eq : (recipe.tree.fill (p.get item)).value = root := by
        simpa [verify, reconstruct, hplan, valid] using accepted
      obtain ⟨ow, opPath, opRoot⟩ := recipe.tree.opens (p.get item) .item opFound
      obtain ⟨bw, bmPath, bmRoot⟩ := recipe.tree.opens (p.get item) .bitmap bmFound
      have bit : activeBit p.chunk loc = true := by
        simp only [fieldsValid, Bool.and_eq_true] at valid
        grind
      refine ⟨⟨ow, bw, p.chunk⟩, bit, ?_, opRoot.trans eq, bmRoot.trans eq⟩
      simp [currentPaths, hplan, opFound, bmFound, opPath, bmPath]
    · simp [verify, reconstruct, hplan, valid] at accepted

end
end Qmdb.Mmb
