module
public import Qmdb.Assumptions

/-! Symbolic openings of the encoded operation and its bitmap chunk under one current root.
A path fixes the projections through the hash inputs. Sibling digests remain under the
prover's control. A valid snapshot supplies the location layout and honest openings. -/

namespace Qmdb.Active
open DY Commonware.Symbolic
@[expose] public section

/-- One projection through a hash input or concatenation, starting from the root. -/
inductive Step where
  /-- Enter a hash preimage. -/
  | hash
  /-- Enter the left side of a concatenation. -/
  | left
  /-- Enter the right side of a concatenation. -/
  | right
  deriving DecidableEq

/-- The public sibling data used to reconstruct a root starting from an opened term. -/
inductive Witness where
  /-- Reach the opened term. -/
  | tip
  /-- Hash the inner term. -/
  | hash (inner : Witness)
  /-- Append the right sibling. -/
  | left (inner : Witness) (rightSibling : Bytes)
  /-- Prepend the left sibling. -/
  | right (leftSibling : Bytes) (inner : Witness)

/-- The path followed by this witness, from the root to the opened term. -/
def Witness.path : Witness → List Step
  | .tip => []
  | .hash w => .hash :: w.path
  | .left w _ => .left :: w.path
  | .right _ w => .right :: w.path

/-- Rehash the path with the prover's siblings and item. -/
def Witness.rebuild (w : Witness) (x : Bytes) : Bytes :=
  match w with
  | .tip => x
  | .hash w => Hash.hash (w.rebuild x)
  | .left w r => Concat.concat (w.rebuild x) r
  | .right l w => Concat.concat l (w.rebuild x)

/-- Equality at the same position forces equality of the opened terms. -/
theorem Witness.binding (a b : Witness) (x y : Bytes) (path : a.path = b.path)
    (eq : a.rebuild x = b.rebuild y) : x = y := by
  induction a generalizing b with
  | tip => cases b <;> simp_all [Witness.path, Witness.rebuild]
  | hash a ih =>
    cases b <;> simp_all [Witness.path, Witness.rebuild]
    exact ih _ rfl (Hash.hash_inj _ _ ‹_›)
  | left a r ih =>
    cases b <;> simp_all [Witness.path, Witness.rebuild]
    exact ih _ rfl (concat_inj ‹_›).1
  | right l a ih =>
    cases b <;> simp_all [Witness.path, Witness.rebuild]
    exact ih _ rfl (concat_inj ‹_›).2

/-- A term occurs at this path under a root. -/
def Opens (path : List Step) (root tip : Bytes) : Prop :=
  ∃ w : Witness, w.path = path ∧ w.rebuild tip = root

/-- The actual fixed chunk width used by Tempo, measured in bytes. -/
abbrev Chunk := Vector UInt8 32

/-- The bitmap bit addressed by an operation location, least significant bit first. -/
def activeBit (chunk : Chunk) (loc : Nat) : Bool :=
  let offset := loc % 256
  chunk[offset / 8]'(by dsimp [offset]; omega) &&& (1 <<< UInt8.ofNat (offset % 8)) != 0

/-- Encode a bitmap chunk as a DyLean literal. -/
def literal (c : Chunk) : Bytes := Literal.literalToBytes ⟨c.toArray⟩

private theorem literal_inj {a b : Chunk} (h : literal a = literal b) : a = b := by
  have eq := congrArg (Literal.bytesToLiteral (Bytes := Bytes)) h
  simp only [literal, Literal.bytesToLiteral_literalToBytes, Option.some.injEq] at eq
  cases a
  cases b
  congr
  exact congrArg ByteArray.data eq

/-- A correctly laid-out snapshot. A missing chunk path denotes an omitted all-zero graft.
The layout is shared by all proofs for this snapshot. -/
structure Snapshot where
  /-- Canonical current root. -/
  root : Bytes
  /-- Committed operation count. -/
  leaves : Nat
  /-- Encoded operation at each in-range location. -/
  item : Nat → Bytes
  /-- Bitmap chunks, indexed by groups of 256 locations. -/
  chunk : Nat → Chunk
  /-- Location of the encoded operation in the root hash input. -/
  itemPath : Nat → List Step
  /-- Location of the bytes of an explicitly committed bitmap chunk. -/
  chunkPath : Nat → Option (List Step)
  /-- The log layout admits an opening to the stored operation. -/
  itemOpening : ∀ l, l < leaves → Opens (itemPath l) root (item l)
  /-- Every exposed chunk agrees with the snapshot bitmap. -/
  chunkOpening : ∀ i p, chunkPath i = some p → Opens p root (literal (chunk i))
  /-- A set bit occurs in a chunk explicitly included in the root. -/
  liveCovered : ∀ l, l < leaves → activeBit (chunk (l / 256)) l = true →
    (chunkPath (l / 256)).isSome

/-- The committed activity of an operation. -/
def Snapshot.live (s : Snapshot) (loc : Nat) : Prop :=
  activeBit (s.chunk (loc / 256)) loc = true

/-- The two openings submitted for a single active operation. -/
structure Proof where
  /-- Path witness for the operation. -/
  operation : Witness
  /-- Path witness for the activity bitmap. -/
  bitmap : Witness
  /-- Claimed bytes of the activity bitmap chunk. -/
  chunk : Chunk

/-- Public position information used by both verification and honest openings. -/
structure Layout where
  /-- Count of operations in the MMB. -/
  leaves : Nat
  /-- Path to the operation at this log location. -/
  itemPath : Nat → List Step
  /-- Path to a committed chunk, when the graft is explicit. -/
  chunkPath : Nat → Option (List Step)

/-- The public part of the snapshot. -/
def Snapshot.layout (s : Snapshot) : Layout := ⟨s.leaves, s.itemPath, s.chunkPath⟩

/-- Acceptance checks the location, the set bit and both reconstructed roots. -/
def Verifies (layout : Layout) (root : Bytes) (loc : Nat) (item : Bytes) (p : Proof) : Prop :=
  loc < layout.leaves ∧ activeBit p.chunk loc = true ∧
  p.operation.path = layout.itemPath loc ∧ p.operation.rebuild item = root ∧
  layout.chunkPath (loc / 256) = some p.bitmap.path ∧ p.bitmap.rebuild (literal p.chunk) = root

/-- The public verifier applied to a snapshot's root and position layout. -/
abbrev Accepts (s : Snapshot) := Verifies s.layout s.root

/-- Every accepted operation is active, in bounds and exactly the committed operation. -/
theorem accepted {s : Snapshot} {loc : Nat} {item : Bytes} {p : Proof}
    (h : Accepts s loc item p) : loc < s.leaves ∧ s.live loc ∧ item = s.item loc := by
  obtain ⟨inside, bit, opPath, opRoot, chunkPath, chunkRoot⟩ := h
  obtain ⟨op, path, eq⟩ := s.itemOpening loc inside
  obtain ⟨bm, bp, br⟩ := s.chunkOpening _ _ chunkPath
  have same := literal_inj (p.bitmap.binding bm _ _ bp.symm (chunkRoot.trans br.symm))
  refine ⟨inside, ?_, p.operation.binding op _ _ (opPath.trans path.symm) (opRoot.trans eq.symm)⟩
  simpa only [Snapshot.live, ← same] using bit

/-- A live location has an accepted honest operation proof. -/
theorem honest (s : Snapshot) {loc : Nat} (inside : loc < s.leaves) (live : s.live loc) :
    ∃ p, Accepts s loc (s.item loc) p := by
  obtain ⟨op, opPath, opRoot⟩ := s.itemOpening loc inside
  obtain ⟨path, hp⟩ := Option.isSome_iff_exists.mp (s.liveCovered _ inside live)
  obtain ⟨bm, bmPath, bmRoot⟩ := s.chunkOpening _ _ hp
  exact ⟨⟨op, bm, s.chunk (loc / 256)⟩, inside, live, opPath, opRoot, bmPath ▸ hp, bmRoot⟩

end
end Qmdb.Active
