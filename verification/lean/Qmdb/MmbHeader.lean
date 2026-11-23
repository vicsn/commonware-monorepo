module
import all DY.EquationalTheory.Hash
public import Qmdb.CurrentRoot
public import Commonware.Symbolic.Wire

/-! Authenticate the dimensions used for proof routing. The MMB root of Tempo's
pinned revision commits to its leaf count and its nonzero inactive peak count. The
canonical current root embeds this grafted root before any pending and partial chunks. -/

namespace Qmdb.Mmb
open DY Commonware.Symbolic
@[expose] public section

/-- An opaque digest supplied to the reader has the wire width of SHA-256. -/
abbrev Digest := { d : Bytes // d.length = 32 }

/-- Public fields and opaque siblings opening the current root to its MMB dimensions. -/
structure Header where
  /-- MMB leaf count. -/
  leaves : UInt64
  /-- Number of peaks in the inactive prefix. -/
  inactive : UInt64
  /-- Empty trees have no inactive prefix. -/
  empty : leaves = 0 → inactive = 0
  /-- Digest of the bagged peaks, used when the tree has leaves. -/
  bag : Digest
  /-- Root of the operations tree. -/
  ops : Digest
  /-- Complete bitmap chunk awaiting grafting. -/
  pending : Option Digest
  /-- First unused bit and digest of a partial bitmap chunk. -/
  tail : Option (UInt64 × Digest)

/-- An integer field in the pinned Merkle and current root encodings. -/
def count (n : UInt64) : Bytes := wireLiteral (writeBE 8 n.toBitVec)

private theorem count_inj {m n : UInt64} (h : count m = count n) : m = n := by
  apply UInt64.toBitVec_inj.mp
  simpa using congrArg (readBE 8) (wireLiteral_injective h)

private theorem count_length (n : UInt64) : (count n).length = 8 := wireLiteral_length _

/-- Pinned MMB root preimage, with the variable-width prefix chosen by root_with_folded_peaks. -/
def Header.input (h : Header) : Bytes :=
  if h.leaves = 0 then count h.leaves
  else Concat.concat (count h.leaves)
    (if h.inactive = 0 then h.bag.val else Concat.concat (count h.inactive) h.bag.val)

/-- The canonical root recomputed from a supplied opening of the MMB dimensions. -/
def Header.root (h : Header) : Bytes :=
  CurrentRoot.term h.ops.val (Hash.hash h.input) (h.pending.map Subtype.val)
    (h.tail.map fun (n, d) => (count n, d.val))

private def firstDigest (r : Bytes) : Bytes :=
  if r.length = 32 then r else ((Concat.split r 32).map Prod.fst).getD r

private theorem first_of_concat (a b : Bytes) (ha : a.length = 32) (hb : 0 < b.length) :
    firstDigest (Concat.concat a b) = a := by
  have split := Concat.split_concat a b
  rw [ha] at split
  simp [firstDigest, ha, Nat.ne_of_gt hb, split]

private def body (h : Header) : Bytes :=
  let g := Hash.hash h.input
  match h.pending, h.tail with
  | none, none => g
  | some p, none => Concat.concat g p.val
  | none, some (n, d) => Concat.concat g (Concat.concat (count n) d.val)
  | some p, some (n, d) => Concat.concat g (Concat.concat p.val (Concat.concat (count n) d.val))

private theorem first_body (h : Header) : firstDigest (body h) = Hash.hash h.input := by
  have width : (Hash.hash h.input).length = 32 := by simp [Hash.hashLength]
  cases hp : h.pending with
  | none =>
    cases ht : h.tail with
    | none => simp [body, hp, ht, firstDigest, width]
    | some nd =>
      obtain ⟨n, d⟩ := nd
      simp only [body, hp, ht]
      exact first_of_concat _ _ width (by simp [count_length])
  | some p =>
    cases ht : h.tail with
    | none =>
      simp only [body, hp, ht]
      exact first_of_concat _ _ width (by rw [p.property]; decide)
    | some nd =>
      obtain ⟨n, d⟩ := nd
      simp only [body, hp, ht]
      exact first_of_concat _ _ width (by simp [count_length])

private theorem root_eq (h : Header) : h.root = Hash.hash (Concat.concat h.ops.val (body h)) := by
  cases hp : h.pending <;> cases ht : h.tail <;> simp [Header.root, CurrentRoot.term, body, hp, ht]

private theorem input_binding (a b : Header) (h : a.input = b.input) :
    a.leaves = b.leaves ∧ a.inactive = b.inactive := by
  unfold Header.input at h
  split_ifs at h with e f g i j <;> first
    | have size := congrArg Bytes.length h
      simp only [Concat.length_concat, count_length, a.bag.property, b.bag.property] at size
      omega
    | exact ⟨count_inj (concat_inj h).1, count_inj (concat_inj (concat_inj h).2).1⟩
    | exact ⟨count_inj (concat_inj h).1, by simp_all⟩
    | exact ⟨count_inj h, by simp_all [a.empty, b.empty]⟩

/-- The verifier may take both dimensions from the proof and recompute its checkpoint root. -/
theorem Header.binding {a b : Header} (same : a.root = b.root) :
    a.leaves = b.leaves ∧ a.inactive = b.inactive := by
  rw [root_eq, root_eq] at same
  have h := congrArg firstDigest (concat_inj (Hash.hash_inj _ _ same)).2
  rw [first_body, first_body] at h
  exact input_binding a b (Hash.hash_inj _ _ h)

end
end Qmdb.Mmb
