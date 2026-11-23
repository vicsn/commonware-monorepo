module
public import Qmdb.Mmb.Plan

/-! Paths through Tempo's pinned MMB Merkle root. This specializes PeakIterator and backward
bagging to a single queried leaf. The Merkle root encoding at Tempo's pin predates the
family/bagging domain bytes on the verification branch. Positions are sibling data on a
hash path: selecting the item or its bitmap never projects into the position field. -/

namespace Qmdb.Mmb
open Active
@[expose] public section

/-- The honest snapshot exposes the pinned verifier's projections. In an omitted all-zero
graft, the first field under the hash is the ordinary Merkle node's 8-byte position. -/
structure Layout (s : Active.Snapshot) (inactive : Nat) : Prop where
  /-- Layout of the honest openings, including zero-chunk identity. -/
  pathsAt : ∀ loc, loc < s.leaves →
    currentPaths s.leaves inactive loc (s.chunk (loc / 256) != Vector.replicate 32 0) =
      some (s.itemPath loc, s.chunkPath (loc / 256))
  /-- The field addressed as a bitmap by a nonzero graft is the node position when omitted. -/
  zeroPosition : ∀ loc item bitmap, loc < s.leaves → loc / 256 < graftedChunks s.leaves →
    s.chunk (loc / 256) = Vector.replicate 32 0 →
    currentPaths s.leaves inactive loc true = some (item, some bitmap) →
    ∃ pos : Vector UInt8 8, Opens bitmap s.root (DY.Literal.literalToBytes ⟨pos.toArray⟩)

/-- Check the submitted paths using only the root, tree dimensions and claimed location. -/
def Accepts (root : DY.Bytes) (leaves inactive loc : Nat) (item : DY.Bytes) (p : Active.Proof) :
    Prop :=
  activeBit p.chunk loc = true ∧
    currentPaths leaves inactive loc true = some (p.operation.path, some p.bitmap.path) ∧
    p.operation.rebuild item = root ∧ p.bitmap.rebuild (literal p.chunk) = root

/-- A position literal and a chunk literal can never be equal. -/
theorem position_ne_chunk (pos : Vector UInt8 8) (chunk : Chunk) :
    DY.Literal.literalToBytes ⟨pos.toArray⟩ ≠ literal chunk := by
  intro same
  have size := congrArg DY.Bytes.length same
  simp [literal, ByteArray.size] at size

/-- Public verification with the authenticated dimensions implies the snapshot-relative check. -/
theorem accepted {s : Active.Snapshot} {inactive loc : Nat} (layout : Layout s inactive)
    {item : DY.Bytes} {p : Active.Proof}
    (h : Accepts s.root s.leaves inactive loc item p) : Active.Accepts s loc item p := by
  obtain ⟨bit, plan, opRoot, bmRoot⟩ := h
  have inside : loc < s.leaves := by
    by_contra! out
    simp [currentPaths, Mmb.plan, show ¬loc < s.leaves by omega] at plan
  have honest := layout.pathsAt loc inside
  have same : currentPaths s.leaves inactive loc true =
      some (s.itemPath loc, s.chunkPath (loc / 256)) := by
    by_cases omitted : s.chunk (loc / 256) = Vector.replicate 32 0
    · by_cases grafted : loc / 256 < graftedChunks s.leaves
      · obtain ⟨pos, w, path, rebuilt⟩ :=
          layout.zeroPosition _ _ _ inside grafted omitted plan
        exact False.elim (position_ne_chunk pos p.chunk
          (w.binding p.bitmap _ _ path (rebuilt.trans bmRoot.symm)))
      · simpa [currentPaths, Mmb.plan, omitted, grafted] using honest
    · have nz : (s.chunk (loc / 256) != Vector.replicate 32 0) = true := bne_iff_ne.mpr omitted
      exact nz ▸ honest
  obtain ⟨opPath, chunkPath⟩ := Prod.mk.inj (Option.some.inj (plan.symm.trans same))
  exact ⟨inside, bit, opPath, opRoot, chunkPath.symm, bmRoot⟩

/-- Every committed live location in a correctly laid-out MMB has a public opening. -/
theorem honest {s : Active.Snapshot} {inactive loc : Nat} (layout : Layout s inactive)
    (inside : loc < s.leaves) (live : s.live loc) : ∃ p, Accepts s.root s.leaves inactive loc
      (s.item loc) p := by
  obtain ⟨p, _, bit, opPath, opRoot, bmPath, bmRoot⟩ := Active.honest s inside live
  have nonzero : s.chunk (loc / 256) ≠ Vector.replicate 32 0 := by
    intro zero
    simp [Active.Snapshot.live, zero, activeBit] at live
  have nz := bne_iff_ne.mpr nonzero
  have plan := layout.pathsAt loc inside
  simp only [Active.Snapshot.layout] at opPath bmPath
  rw [nz, ← opPath, bmPath] at plan
  exact ⟨p, bit, plan, opRoot, bmRoot⟩

end
end Qmdb.Mmb
