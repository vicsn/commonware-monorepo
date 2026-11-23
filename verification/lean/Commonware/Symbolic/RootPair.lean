module
public import Commonware.Symbolic.Terms

/-! An ordered pair of database roots committed with a single SHA-256 operation. -/

namespace Commonware.Symbolic
open DY
@[expose] public section

variable [BytesFunctor] [BytesFunctor.Has Hash.SubF] [BytesFunctor.Has Concat.SubF] [BytesLength]

/-- The digest of the concatenation of two fixed-width database roots, in application order. -/
def rootPair (first second : Bytes) : Bytes :=
  Hash.hash (Concat.concat first second)

/-- An opening of the outer commitment uniquely determines both database roots in order. -/
theorem rootPair_binding {a b c d : Bytes} (h : rootPair a b = rootPair c d) :
    a = c ∧ b = d :=
  concat_inj (Hash.hash_inj _ _ h)

end
end Commonware.Symbolic
