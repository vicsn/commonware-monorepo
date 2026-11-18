module
public import QmdbDylean.Extraction
public import Model

/-! Trusted glue between the extracted Rust and DyLean. `dyTerms` interprets the specification's
terms with DyLean's symbolic literal, concatenation and hash constructors. `Snapshot` is the
authenticated historical snapshot that the application supplies, and `snapshotStore` exposes it
to the extracted code. -/

namespace Qmdb
open DY Aeneas Aeneas.Std CoreModels
@[expose] public section

/-- The bytes of a Rust byte slice. -/
def toByteArray (s : Slice Std.U8) : ByteArray :=
  ⟨(s.val.map fun b => UInt8.ofNat b.val).toArray⟩

/-- Rust terms as DyLean terms: digests are terms and items are literals. -/
def dyTerms : qmdb_dylean.terms.Terms Unit Bytes Bytes ByteArray where
  coremarkerCopyInst := ⟨⟨RustM.ok, fun _ x => RustM.ok x⟩⟩
  corecmpPartialEqInst :=
    { eq := fun a b => RustM.ok (decide (a = b)), ne := fun a b => RustM.ok (!decide (a = b)) }
  literal s := RustM.ok (Literal.literalToBytes (toByteArray s))
  item x := RustM.ok (Literal.literalToBytes x)
  digest d := RustM.ok d
  parse m := RustM.ok (match Literal.bytesToLiteral m with
    | some x => core.option.Option.Some x
    | none => core.option.Option.None)
  concat a b := RustM.ok (Concat.concat a b)
  hash x := RustM.ok (Hash.hash x)

/-- A fixed, authenticated historical snapshot with `2^height` leaves. -/
class Snapshot where
  items : Nat → ByteArray
  height : Std.U32

/-- The snapshot's items, as the extracted code reads them. -/
def snapshotStore [Snapshot] : qmdb_dylean.terms.Store Unit ByteArray where
  item _ location := RustM.ok (Snapshot.items location.val)

end
end Qmdb
