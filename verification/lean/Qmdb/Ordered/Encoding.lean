module
public import Commonware.Symbolic.Wire
public import Commonware.Symbolic.RustM
public import Qmdb.CurrentRoot
public import Qmdb.Ordered

/-! The fixed encoding of an ordered operation as production's extracted layout writes it: its
tag, its fields, then zeros up to the width of the widest operation. Checked by Lean. -/

namespace Qmdb.Ordered.Layout
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-- Fixed-width, injective byte encodings of keys and values, as the database's codec writes
them. -/
structure Codec (K V : Type) where
  /-- Width of an encoded key. -/
  keyWidth : Nat
  /-- Width of an encoded value. -/
  valueWidth : Nat
  /-- The bytes of a key. -/
  key : K → List Std.U8
  /-- The bytes of a value. -/
  value : V → List Std.U8
  /-- Every key has the key width. -/
  keyLen : ∀ k, (key k).length = keyWidth
  /-- Every value has the value width. -/
  valueLen : ∀ v, (value v).length = valueWidth
  /-- Distinct keys have distinct bytes. -/
  keyInj : Function.Injective key
  /-- Distinct values have distinct bytes. -/
  valueInj : Function.Injective value
  /-- The widths fit the machine's sizes. -/
  small : 2 * keyWidth + valueWidth + 16 < 2 ^ 32

variable {K V : Type} (c : Codec K V)

/-- The width every operation is padded to: the widest of an update, a commit and a delete. -/
def total : Nat :=
  max (max (1 + (2 * c.keyWidth + c.valueWidth)) (1 + 1 + c.valueWidth + 8)) (1 + c.keyWidth)

/-- `n` zero bytes. -/
def zeros (n : Nat) : List Std.U8 := List.replicate n 0#u8

/-- The big-endian bytes of a 64-bit integer. -/
def word (x : Std.U64) : List Std.U8 := (Aeneas.Std.core.num.U64.to_be_bytes x).to_slice.val

theorem word_length (x : Std.U64) : (word x).length = 8 := by
  simp [word, Array.to_slice]

/-- The bytes production writes for an operation. -/
def bytes : Operation K V → List Std.U8
  | .update k v n => [tags.UPDATE_CONTEXT] ++ c.key k ++ c.value v ++ c.key n ++
      zeros (total c - (1 + (2 * c.keyWidth + c.valueWidth)))
  | .delete k => [tags.DELETE_CONTEXT] ++ c.key k ++ zeros (total c - (1 + c.keyWidth))
  | .commit m f => [tags.COMMIT_CONTEXT] ++
      (match m with
        | none => zeros (1 + c.valueWidth)
        | some v => [1#u8] ++ c.value v) ++
      word ⟨f.toBitVec⟩ ++ zeros (total c - (1 + 1 + c.valueWidth + 8))

/-- A DyLean literal of bytes, as production's hasher reads a byte slice. -/
def literal (L : List Std.U8) : Bytes :=
  Literal.literalToBytes ⟨(L.map fun b => UInt8.ofNat b.val).toArray⟩

theorem literal_inj {a b : List Std.U8} (h : literal a = literal b) : a = b := by
  have same := congrArg (Literal.bytesToLiteral (Bytes := Bytes)) h
  simp only [literal, Literal.bytesToLiteral_literalToBytes, Option.some.injEq,
    ByteArray.mk.injEq] at same
  have lists := congrArg Array.toList same
  simp at lists
  refine List.map_injective_iff.mpr ?_ lists
  intro x y e
  apply UScalar.eq_of_val_eq
  have hx : x.val < 256 := by scalar_tac
  have hy : y.val < 256 := by scalar_tac
  have := congrArg (fun u : UInt8 => u.toBitVec.toNat) e
  simp [UInt8.ofNat] at this
  omega

theorem word_inj {x y : Std.U64} (h : word x = word y) : x = y := by
  have s : Verifier.be x = Verifier.be y := Slice.ext _ _ h
  have w := congrArg (fun s => part (.Bytes s)) s
  simp only [CurrentRoot.be_wire] at w
  have bv := congrArg (readBE 8) (wireLiteral_injective w)
  simp only [read_write] at bv
  exact UScalar.eq_of_val_eq (congrArg BitVec.toNat bv)

/-- The tag an operation's bytes start with. -/
def tag : Operation K V → Std.U8
  | .update .. => tags.UPDATE_CONTEXT
  | .delete _ => tags.DELETE_CONTEXT
  | .commit .. => tags.COMMIT_CONTEXT

theorem bytes_head (op : Operation K V) : (bytes c op).head? = some (tag op) := by
  cases op <;> simp [bytes, tag]

/-- Distinct operations have distinct bytes. -/
theorem bytes_inj : Function.Injective (bytes c) := by
  intro a b eq
  have ht := congrArg List.head? eq
  rw [bytes_head, bytes_head] at ht
  cases a <;> cases b <;>
    simp [tag, tags.UPDATE_CONTEXT, tags.DELETE_CONTEXT, tags.COMMIT_CONTEXT] at ht <;>
    simp only [bytes] at eq
  · rename_i k v n k' v' n'
    obtain ⟨e₁, -⟩ := List.append_inj' eq rfl
    obtain ⟨e₂, hn⟩ := List.append_inj' e₁ (by simp [c.keyLen])
    obtain ⟨e₃, hv⟩ := List.append_inj' e₂ (by simp [c.valueLen])
    obtain ⟨-, hk⟩ := List.append_inj' e₃ (by simp [c.keyLen])
    rw [c.keyInj hk, c.valueInj hv, c.keyInj hn]
  · rename_i k k'
    obtain ⟨e₁, -⟩ := List.append_inj' eq rfl
    obtain ⟨-, hk⟩ := List.append_inj' e₁ (by simp [c.keyLen])
    rw [c.keyInj hk]
  · rename_i m f m' f'
    have metaLen : ∀ x : Option V, (match x with
        | none => zeros (1 + c.valueWidth)
        | some v => [1#u8] ++ c.value v).length = 1 + c.valueWidth := by
      intro x; cases x <;> simp [zeros, c.valueLen]; omega
    obtain ⟨e₁, -⟩ := List.append_inj' eq rfl
    obtain ⟨e₂, hf⟩ := List.append_inj' e₁ (by simp [word_length])
    obtain ⟨-, hm⟩ := List.append_inj' e₂ (by rw [metaLen, metaLen])
    have floors : f = f' := by
      have := congrArg UScalar.bv (word_inj hf)
      exact UInt64.toBitVec_inj.mp this
    have metas : m = m' := by
      cases m <;> cases m'
      · rfl
      · exfalso; have := congrArg List.head? hm
        simp [zeros, Nat.add_comm 1, List.replicate_succ] at this
      · exfalso; have := congrArg List.head? hm
        simp [zeros, Nat.add_comm 1, List.replicate_succ] at this
      · rename_i v v'
        simp only [List.singleton_append, List.cons.injEq, true_and] at hm
        rw [c.valueInj hm]
    rw [metas, floors]

/-- The fixed encoding of ordered operations: the literal of their bytes. -/
def encoding : Encoding K V :=
  ⟨fun op => literal (bytes c op), fun _ _ h => bytes_inj c (literal_inj h)⟩

/-! ## The extracted layout writes these bytes -/

/-- A writer that appends to a byte list: one byte, zeros, a big-endian word, or a key's or a
value's codec bytes. This is how production's fixed codec fills its buffer. -/
def baseWriter : layout.Writer (List Std.U8) K V (ordered.Update K V V) where
  byte w b := RustM.ok (w ++ [b])
  zeros w n := RustM.ok (w ++ zeros n.val)
  word w x := RustM.ok (w ++ word x)
  key w k := RustM.ok (w ++ c.key k)
  value w v := RustM.ok (w ++ c.value v)
  update w _ := RustM.ok w

/-- The byte-list writer whose update payload is laid out by production's
`write_ordered_update`. -/
def writer : layout.Writer (List Std.U8) K V (ordered.Update K V V) :=
  { baseWriter c with
    update := fun w u => layout.write_ordered_update (baseWriter c) w u.key u.value u.next_key }

/-- The widths production's fixed ordered codec computes for these keys and values. -/
def widths : layout.Widths :=
  ⟨⟨BitVec.ofNat _ c.keyWidth⟩, ⟨BitVec.ofNat _ c.valueWidth⟩,
    ⟨BitVec.ofNat _ (2 * c.keyWidth + c.valueWidth)⟩⟩

theorem usize_val (n : Nat) (small : n < 2 ^ 32) :
    (⟨BitVec.ofNat _ n⟩ : Std.Usize).val = n := by
  have wide : 2 ^ 32 ≤ 2 ^ System.Platform.numBits :=
    Nat.pow_le_pow_right (by decide) (by cases System.Platform.numBits_eq <;> simp [*])
  change (BitVec.ofNat _ n).toNat = n
  simp only [BitVec.toNat_ofNat, UScalarTy.numBits]
  apply Nat.mod_eq_of_lt
  omega

theorem widths_key : (widths c).key.val = c.keyWidth :=
  usize_val _ (by have := c.small; omega)

theorem widths_value : (widths c).value.val = c.valueWidth :=
  usize_val _ (by have := c.small; omega)

theorem widths_update : (widths c).update.val = 2 * c.keyWidth + c.valueWidth :=
  usize_val _ (by have := c.small; omega)

/-- The width production pads every operation to. -/
theorem total_ok : ∃ t : Std.Usize, layout.Widths.total (widths c) = RustM.ok t ∧
    t.val = total c := by
  have small := c.small
  have kv := widths_key c
  have vv := widths_value c
  have uv := widths_update c
  obtain ⟨u, hu, uv'⟩ := add_ok 1#usize (widths c).update (by rw [uv]; scalar_tac)
  obtain ⟨t₁, ht₁, t₁v⟩ := add_ok 1#usize 1#usize (by scalar_tac)
  obtain ⟨t₂, ht₂, t₂v⟩ := add_ok t₁ (widths c).value (by simp at t₁v; rw [t₁v, vv]; scalar_tac)
  obtain ⟨cm, hcm, cmv⟩ := add_ok t₂ 8#usize (by simp at t₁v t₂v; rw [t₂v, t₁v, vv]; scalar_tac)
  obtain ⟨d, hd, dv⟩ := add_ok 1#usize (widths c).key (by rw [kv]; scalar_tac)
  simp only [uv, vv, kv] at uv' t₂v dv
  simp at uv' t₁v t₂v cmv dv
  have base : layout.Widths.total (widths c) =
      (if u.val < cm.val then (if cm.val < d.val then RustM.ok d else RustM.ok cm)
       else (if u.val < d.val then RustM.ok d else RustM.ok u)) := by
    by_cases h₁ : u.val < cm.val <;> by_cases h₂ : cm.val < d.val <;>
      by_cases h₃ : u.val < d.val <;>
      simp [layout.Widths.total, layout.Widths.update_operation, layout.Widths.commit,
        layout.Widths.delete, hu, ht₁, ht₂, hcm, hd, h₁, h₂, h₃]
  rw [base]
  simp only [total, Nat.max_def]
  split_ifs <;> exact ⟨_, rfl, by omega⟩

/-- The journal operation an extracted ordered operation stands for. -/
def readOp : ordered.Operation Std.U64 K V V → Operation K V
  | .Update u => .update u.key u.value u.next_key
  | .Commit m f => .commit m ⟨f.bv⟩

/-- Production's fixed encoding of an ordered operation writes exactly its bytes. -/
theorem encode_ok (keyInst : ordered.Key K) (valueInst : ordered.ValueEncoding V V)
    (op : ordered.Operation Std.U64 K V V) :
    ordered.encode keyInst valueInst (writer c) [] (widths c) op =
      RustM.ok (bytes c (readOp op)) := by
  have small := c.small
  obtain ⟨t, ht, tv⟩ := total_ok c
  have big : 1 + (2 * c.keyWidth + c.valueWidth) ≤ total c ∧
      1 + 1 + c.valueWidth + 8 ≤ total c := by
    simp only [total]; omega
  cases op with
  | Update u =>
    obtain ⟨w, hw, wv⟩ := add_ok 1#usize (widths c).update (by rw [widths_update]; scalar_tac)
    simp only [widths_update] at wv
    obtain ⟨z, hz, zv⟩ := sub_ok t w (by simp at wv; omega)
    simp [ordered.encode, layout.write_fixed, ht, writer, baseWriter, layout.write_ordered_update,
      layout.Widths.update_operation, hw, hz, bytes, readOp]
    simp at zv wv
    rw [zv, tv, wv]
  | Commit m f =>
    obtain ⟨t₁, ht₁, t₁v⟩ := add_ok 1#usize 1#usize (by scalar_tac)
    obtain ⟨t₂, ht₂, t₂v⟩ := add_ok t₁ (widths c).value
      (by simp at t₁v; rw [t₁v, widths_value]; scalar_tac)
    obtain ⟨cm, hcm, cmv⟩ := add_ok t₂ 8#usize
      (by simp at t₁v t₂v; rw [t₂v, t₁v, widths_value]; scalar_tac)
    simp only [widths_value] at t₂v
    simp at t₁v t₂v cmv
    obtain ⟨z, hz, zv⟩ := sub_ok t cm (by omega)
    obtain ⟨o, ho, ov⟩ := add_ok 1#usize (widths c).value (by rw [widths_value]; scalar_tac)
    simp only [widths_value] at ov
    simp at ov zv
    cases m with
    | none =>
      simp [ordered.encode, layout.write_fixed, ht, writer, baseWriter, layout.Widths.commit, ht₁,
        ht₂, hcm, hz, ho, bytes, readOp, ov, zv, tv, t₂v, t₁v, cmv]
    | some v =>
      simp [ordered.encode, layout.write_fixed, ht, writer, baseWriter, layout.Widths.commit, ht₁,
        ht₂, hcm, hz, bytes, readOp, zv, tv, t₂v, t₁v, cmv]

end
end Qmdb.Ordered.Layout
