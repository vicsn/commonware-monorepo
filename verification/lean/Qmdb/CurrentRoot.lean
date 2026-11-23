module
public import Qmdb.Active
public import Qmdb.Verifier
public import Commonware.Symbolic.Wire

/-! How the current root of a grafted MMB places its two suffix contributions.
The path for a pending or partial chunk reaches its digest. One further hash projection
reaches its literal bytes. -/

namespace Qmdb.CurrentRoot
open DY Active
@[expose] public section

/-- Symbolic form of the four preimages in current::db::combine_roots. The trailing pair
contains the big-endian next bit and the partial chunk digest. -/
def term (ops grafted : Bytes) (pending : Option Bytes) (tail : Option (Bytes × Bytes)) : Bytes :=
  Hash.hash (Concat.concat ops (match pending, tail with
    | none, none => grafted
    | some p, none => Concat.concat grafted p
    | none, some (n, d) => Concat.concat grafted (Concat.concat n d)
    | some p, some (n, d) => Concat.concat grafted (Concat.concat p (Concat.concat n d))))

/-- The extracted production root builder hashes exactly this ordered symbolic input. -/
theorem extracted (ops g : Bytes) (pending : Option Bytes)
    (tail : Option (Aeneas.Std.U64 × Bytes)) :
    commonware_symbolic.terms.current_root Commonware.Symbolic.dyTerms () ops g
        pending tail =
      Aeneas.Std.RustM.ok (term ops g pending (tail.map fun (n, d) =>
        (Commonware.Symbolic.part (.Bytes (Verifier.be n)), d))) := by
  cases pending <;> rcases tail with _ | ⟨n, d⟩ <;>
    simp [commonware_symbolic.terms.current_root, term,
      Verifier.to_be_bytes_ok, Verifier.be, CoreModels.core.array.Array.as_slice,
      Commonware.Symbolic.dyTerms, Commonware.Symbolic.part,
      CoreModels.rust_primitives.slice.array_as_slice,
      Commonware.Symbolic.chain]

open Commonware.Symbolic Aeneas Aeneas.Std in
/-- The extracted eight-byte big-endian count agrees with the wire codec. -/
theorem be_wire (n : Std.U64) :
    part (.Bytes (Verifier.be n)) = wireLiteral (writeBE 8 n.bv) := by
  simp only [part, wireLiteral]
  congr 1
  apply ByteArray.ext
  apply _root_.Array.ext'
  simp [toByteArray, Verifier.be, Std.core.num.U64.to_be_bytes, Array.to_slice,
    Std.Array.from_val, BitVec.toBEBytes]
  change _ = (writeBE 8 n.bv).toList
  have fold (k : Nat) (v : BitVec (8 * k)) :
      (v.toLEBytes.map fun b => UInt8.ofNat b.toNat).reverse = (writeBE k v).toList := by
    induction k with
    | zero => simp [writeBE, BitVec.toLEBytes]
    | succ k ih =>
      rw [writeBE, BitVec.toLEBytes]
      simp only [Nat.mul_pos_iff_of_pos_left (by decide : 0 < 8), Nat.zero_lt_succ,
        ↓reduceIte, List.map_cons, List.reverse_cons, Vector.toList_push, ih]
      congr 2
      · apply congrArg (writeBE k)
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
          BitVec.extractLsb']
        rfl
      · apply UInt8.toBitVec_inj.mp
        apply BitVec.eq_of_toNat_eq
        simp [UInt8.ofNat]
  exact fold 8 n.bv


open Commonware.Symbolic Aeneas Aeneas.Std in
/-- The production hash builder accepts the wire literal used by the public MMB header. -/
theorem extracted_wire (ops g : Bytes) (p : Option Bytes) (t : Option (Std.U64 × Bytes)) :
    commonware_symbolic.terms.current_root dyTerms () ops g p t =
      RustM.ok (term ops g p (t.map fun (n, d) => (wireLiteral (writeBE 8 n.bv), d))) := by
  simpa only [be_wire] using extracted ops g p t

/-- Path to the grafted Merkle root in each of the four layouts. -/
def graftedPath (pending tail : Bool) : List Step :=
  if pending || tail then [.hash, .right, .left] else [.hash, .right]

/-- Path to the digest of a complete chunk awaiting its grafting ancestor. -/
def pendingPath (tail : Bool) : List Step :=
  if tail then [.hash, .right, .right, .left] else [.hash, .right, .right]

/-- Path to the digest of a trailing incomplete chunk. -/
def partialPath (pending : Bool) : List Step :=
  if pending then [.hash, .right, .right, .right, .right] else [.hash, .right, .right, .right]

/-- The canonical root opens to the grafted Merkle root. -/
theorem opens_grafted (o g : Bytes) (p : Option Bytes) (t : Option (Bytes × Bytes)) :
    Opens (graftedPath p.isSome t.isSome) (term o g p t) g := by
  cases p <;> cases t with
  | none =>
    first
    | exact ⟨.hash (.right o .tip), rfl, rfl⟩
    | exact ⟨.hash (.right o (.left .tip _)), rfl, rfl⟩
  | some nd =>
    cases nd
    exact ⟨.hash (.right o (.left .tip _)), rfl, rfl⟩

/-- A present pending digest opens in the same root, independently of the partial chunk. -/
theorem opens_pending (o g d : Bytes) (t : Option (Bytes × Bytes)) :
    Opens (pendingPath t.isSome) (term o g (some d) t) d := by
  cases t with
  | none => exact ⟨.hash (.right o (.right g .tip)), rfl, rfl⟩
  | some nd =>
    cases nd
    exact ⟨.hash (.right o (.right g (.left .tip _))), rfl, rfl⟩

/-- A present partial digest opens in the same root, independently of the pending chunk. -/
theorem opens_partial (o g n d : Bytes) (p : Option Bytes) :
    Opens (partialPath p.isSome) (term o g p (some (n, d))) d := by
  cases p with
  | none => exact ⟨.hash (.right o (.right g (.right n .tip))), rfl, rfl⟩
  | some p => exact ⟨.hash (.right o (.right g (.right p (.right n .tip)))), rfl, rfl⟩

/-- Production's special case for a fully inactive chunk. -/
def graft (chunk : Chunk) (subtree : Bytes) : Bytes :=
  if chunk = Vector.replicate 32 0 then subtree
  else Hash.hash (Concat.concat (literal chunk) subtree)

/-- A set bit guarantees that a graft explicitly commits to this chunk. -/
theorem opens_graft {chunk : Chunk} {loc : Nat} (live : activeBit chunk loc = true)
    (subtree : Bytes) : Opens [.hash, .left] (graft chunk subtree) (literal chunk) := by
  have nonzero : chunk ≠ Vector.replicate 32 0 := by
    rintro rfl
    simp [activeBit] at live
  exact ⟨.hash (.left .tip subtree), rfl, by simp [graft, nonzero, Witness.rebuild]⟩

/-- An explicit graft around a subtree has a 32-byte first field. A plain node has an
8-byte position there. Even an adversarial subtree cannot equate these preimages. -/
theorem graft_ne_plain (c : Chunk) (pos : Vector UInt8 8) (sub l r : Bytes) :
    Hash.hash (Concat.concat (literal c) sub) ≠
      Hash.hash (Concat.concat (Literal.literalToBytes ⟨pos.toArray⟩) (Concat.concat l r)) := by
  intro h
  have eq := (Commonware.Symbolic.concat_inj (Hash.hash_inj _ _ h)).1
  have bytes := congrArg (Literal.bytesToLiteral (Bytes := Bytes)) eq
  simp only [literal, Literal.bytesToLiteral_literalToBytes, Option.some.injEq] at bytes
  have := congrArg ByteArray.size bytes
  simp [ByteArray.size] at this

end
end Qmdb.CurrentRoot
