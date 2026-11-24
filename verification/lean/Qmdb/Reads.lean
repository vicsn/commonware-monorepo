module
public import Qmdb.Ordered.Encoding
public import Qmdb.Mmb.Extracted

/-! The extracted ordered client's operation check: it encodes the operation with production's
fixed layout and accepts only what the extracted current verifier accepts. Checked by Lean. -/

namespace Qmdb.Reads
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
open Qmdb.Ordered Qmdb.Ordered.Layout
@[expose] public section

variable {K V : Type} (c : Codec K V)

/-- The byte list a writer holds, as the byte slice the client hashes. -/
def asSlice : CoreModels.core.convert.AsRef (List Std.U8) (Slice Std.U8) :=
  ⟨fun w => if h : w.length ≤ Usize.max then RustM.ok (Slice.from w h)
    else CoreModels.core.panicking.internal.panic _⟩

/-- The current-proof fields of an ordered operation proof. -/
def fieldsOf (proof : reads.OperationProof Std.U64 Bytes (reads.Payload Bytes)) :
    current.Fields Bytes :=
  ⟨proof.payload.2.leaves, proof.payload.2.inactive, proof.payload.2.digests, proof.payload.1,
    proof.payload.2.pending, proof.payload.2.partial⟩

theorem bytes_small (op : Operation K V) : (bytes c op).length ≤ Usize.max := by
  have small := c.small
  have wide : 2 ^ 32 ≤ 2 ^ System.Platform.numBits :=
    Nat.pow_le_pow_right (by decide) (by cases System.Platform.numBits_eq <;> simp [*])
  have maxv : Usize.max = 2 ^ System.Platform.numBits - 1 := by
    simp [Usize.max, Usize.numBits]
  have len : (bytes c op).length ≤ 2 * c.keyWidth + c.valueWidth + 16 := by
    cases op with
    | update k v n => simp [bytes, zeros, c.keyLen, c.valueLen, total]; omega
    | delete k => simp [bytes, zeros, c.keyLen, total]; omega
    | commit m f =>
      cases m <;> simp [bytes, zeros, c.valueLen, word_length, total] <;> omega
  omega

/-- Soundness of the extracted ordered client's operation check: an operation it accepts at a
proof's location opens the trusted root, encoded with production's fixed layout, along the paths
`Plan` assigns to that location. -/
theorem verify_selected_sound (keyInst : reads.Key K) (valueInst : reads.ValueEncoding V V)
    (digestInst : reads.Digest Bytes)
    (proof : reads.OperationProof Std.U64 Bytes (reads.Payload Bytes))
    (op : reads.Operation Std.U64 K V V) (root : Bytes) (chunk : Active.Chunk)
    (hchunk : proof.payload.2.chunk = Mmb.Extracted.chunkSlice chunk)
    (wide : Mmb.Extracted.Wide (fieldsOf proof))
    (acc : reads.verify_selected keyInst valueInst dyTerms digestInst (writer c) asSlice ()
      (widths c) [] proof op root = RustM.ok true) :
    ∃ w, Mmb.Accepts root proof.payload.2.leaves.val proof.payload.2.inactive.val proof.loc.val
      ((encoding c) (readOp op)) w := by
  obtain ⟨loc, t, p⟩ := proof
  simp only at hchunk
  unfold reads.verify_selected at acc
  simp only [encode_ok, bind_ok, asSlice, bytes_small, ↓reduceDIte] at acc
  simp [hchunk] at acc
  obtain ⟨w, accepts⟩ := Mmb.Extracted.verify_operation_sound (fieldsOf ⟨loc, t, p⟩) loc chunk _
    root wide acc
  have item : part (.Bytes (Slice.from (bytes c (readOp op)) (bytes_small c _))) =
      (encoding c) (readOp op) := by
    simp [part, toByteArray, encoding, literal, Slice.from_val]
  exact ⟨w, item ▸ accepts⟩

end
end Qmdb.Reads
