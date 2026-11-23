module
public import Commonware.Symbolic.Wire
public import Qmdb.Ordered

/-! Symbolic fixed operation preimages for a 32-byte key and an n-byte value.
The update is longest at 1 + 32 + n + 32 bytes. Deletes end with n + 32 zero
bytes and commits end with 55 zero bytes. -/

namespace Qmdb.Ordered
open DY Commonware.Symbolic
@[expose] public section

/-- A one-byte operation or presence tag. -/
def byte (b : UInt8) : Bytes := wireLiteral (#v[b] : Wire 1)
/-- Fixed zero padding. -/
def zeros (n : Nat) : Bytes := wireLiteral (Vector.replicate n (0 : UInt8))
/-- The eight-byte floor in network byte order. -/
def floorBe (n : UInt64) : Bytes := wireLiteral (writeBE 8 n.toBitVec)

private theorem byte_inj {a b : UInt8} (h : byte a = byte b) : a = b := by
  have same := wireLiteral_injective h
  exact congrArg (fun v : Wire 1 => v[0]) same

private theorem floor_inj {a b : UInt64} (h : floorBe a = floorBe b) : a = b := by
  have same := congrArg (readBE 8) (wireLiteral_injective h)
  apply UInt64.toBitVec_inj.mp
  simpa [floorBe] using same

/-- The presence byte followed by metadata or zero padding of equal width. -/
def metadata (n : Nat) : Option (Wire n) → Bytes
  | none => Concat.concat (byte 0) (zeros n)
  | some v => Concat.concat (byte 1) (wireLiteral v)

private theorem metadata_inj {n : Nat} : Function.Injective (metadata n) := by
  intro a b eq
  cases a <;> cases b <;> first
    | rfl
    | exact congrArg some (wireLiteral_injective (concat_inj eq).2)
    | have h := byte_inj (concat_inj eq).1; contradiction

/-- Production fixed ordered fields, tags, zero padding and big-endian commit floor. -/
def operationTerm (key : K ↪ Bytes) (n : Nat) : Operation K (Wire n) → Bytes
  | .update k value next => Concat.concat (byte 0xd2)
      (Concat.concat (key k) (Concat.concat (wireLiteral value) (key next)))
  | .delete k => Concat.concat (byte 0xd1) (Concat.concat (key k) (zeros (n + 32)))
  | .commit m floor => Concat.concat (byte 0xd3)
      (Concat.concat (metadata n m) (Concat.concat (floorBe floor) (zeros 55)))

/-- Each tag and each active payload field is recoverable from the operation term. -/
theorem operationTerm_inj (key : K ↪ Bytes) (n : Nat) :
    Function.Injective (operationTerm key n) := by
  intro a b eq
  cases a <;> cases b <;> first
    | have neq := byte_inj (concat_inj eq).1; contradiction
    | exact congrArg Operation.delete (key.injective (concat_inj (concat_inj eq).2).1)
    | have fields := concat_inj (concat_inj eq).2
      obtain rfl := key.injective fields.1
      obtain rfl := wireLiteral_injective (concat_inj fields.2).1
      obtain rfl := key.injective (concat_inj fields.2).2
      rfl
    | have fields := concat_inj (concat_inj eq).2
      obtain rfl := metadata_inj fields.1
      obtain rfl := floor_inj (concat_inj fields.2).1
      rfl

/-- All three encoded variants have the update's fixed width. -/
theorem operationTerm_length (key : K ↪ Bytes) (n : Nat) (width : ∀ k, (key k).length = 32)
    (op : Operation K (Wire n)) : (operationTerm key n op).length = 65 + n := by
  cases op with
  | commit m f =>
    cases m <;> simp [operationTerm, metadata, byte, zeros, floorBe] <;> omega
  | update | delete => simp [operationTerm, width, byte, zeros]; omega

/-- Fixed ordered operations with 32-byte keys are injective under symbolic concatenation. -/
def fixedEncoding (key : K ↪ Bytes) (n : Nat) : Encoding K (Wire n) :=
  ⟨operationTerm key n, operationTerm_inj key n⟩

end
end Qmdb.Ordered
