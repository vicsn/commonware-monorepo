module
public import DY.EquationalTheory.Hash

/-! Ideal Keccak-256 as a unary DyLean constructor with a 32-byte result. Applications
can include it alongside the standard hash constructor used for SHA-256. -/

namespace Commonware.Symbolic.Keccak
open DY
@[expose] public section

namespace Keccak

/-- The preimage of an ideal Keccak digest. -/
structure SubF (B : Type) where
  /-- Input bytes. -/
  input : B

instance : ALaCarte.FunctorSizeOf SubF where
  sizeOf | ⟨input⟩ => sizeOf input

instance : ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 1 }
  toRepr | ⟨input⟩ => { id := (), data := (), as := #v[input] }
  fromRepr | { id, as, .. } => ⟨as[0]⟩
  from_to | ⟨_⟩ => rfl
  to_from | { id, data, as } => by simp_all <;> grind
  sizeOf_eq | ⟨_⟩ => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

instance : ALaCarte.RepresentableDecidableEq SubF where
instance : ALaCarte.RepresentableOrd SubF where
instance : SubBytesFunctor SubF where

/-- The wire width of a Keccak digest. -/
def SubF.length [BytesFunctor] : Bytes.PartialLength SubF := fun _ _ => 32

end Keccak

#combine into BytesFunctor, BytesLength from
  Keccak,

/-- The ideal digest of the given input. -/
def digest [BytesFunctor] [BytesFunctor.Has SubF] (input : Bytes) : Bytes :=
  BytesView.pack (⟨input⟩ : Keccak.SubF Bytes)

theorem digest_inj [BytesFunctor] [BytesFunctor.Has SubF] {a b : Bytes}
    (h : digest a = digest b) : a = b := by
  unfold digest at h
  grind

@[simp] theorem digest_length [BytesFunctor] [BytesFunctor.Has SubF] [BytesLength]
    [BytesLength.Has SubF.length] (a : Bytes) : (digest a).length = 32 := by
  unfold digest
  grind [Keccak.SubF.length]

/-- Anyone knowing a preimage can compute its digest. -/
def digest.attackerKnowledge
    [BytesFunctor]
    [BytesFunctor.Has SubF] :
    SubAttackerKnowledge SubF where
  pred p out := ∃ input, out = digest input ∧ p input

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  digest,

section
variable [ExecTraceTypes] [ProofTraceTypes] [BytesFunctor]

/-- A hash inherits its input's trace invariant and security label. -/
def Keccak.invariants : Bytes.PartialInvariants Keccak.SubF where
  well_formed := fun x rec => rec x.input
  usage := fun _ _ _ => Usage.nothing
  label := fun x rec => rec x.input
  invariant := fun x rec => rec x.input

theorem Keccak.invariantsProofs
    [BytesInvariants] :
    Bytes.PartialInvariantsProofs Keccak.invariants where

end

#combine into BytesInvariants, BytesInvariantsProofs from
  Keccak,

section
variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesFunctor.Has SubF] [BytesInvariants] [BytesInvariants.Has invariants]

instance : SubAttackerKnowledgeTheorem digest.attackerKnowledge where
  pf := by
    intro out tr _ ⟨input, eq, known⟩
    subst out
    simpa [Bytes.Publishable, digest, Bytes.Invariant.eq, Bytes.label.eq,
      Keccak.invariants] using known

end

#combine [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into
  SubAttackerKnowledgeTheorem' from
  digest,

end
end Commonware.Symbolic.Keccak
