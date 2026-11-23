module
public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.Trace.Manipulation
import DY.Meta

/-! Message authentication codes as a constructor of DyLean's terms, for targets whose Rust
confirms a key by sending a value derived from it. DyLean has theories for hashing, signatures
and key derivation and none for a keyed value that carries a claim.

Trusted: `mac` is a free constructor of a key and a message, so a code is equal only to the code
of the same key and message, and `mac.attackerKnowledge` is the one way the attacker obtains a
code: by computing it from a key and a message that it knows. The attacker cannot take a code
apart. A code is checked by computing it again and comparing.

Checked: `attacker_knows_mac`, which shows that the attacker's rule applies, and the invariant.
A code is as public as its message, and a valid code either satisfies the predicate `MacPred`
that a protocol attaches to its codes, or its key is known to the attacker. `mac_invariant` is
what a protocol proves before it sends a code, and `mac_checked` is what it learns from a code
that it received and recomputed. -/

namespace Commonware.Symbolic.Mac
open DY

/-- Terms that have message authentication codes. -/
public class CanMac (Bytes : Type u) where
  /-- The code of `msg` under `key`. -/
  mac : (key msg : Bytes) → Bytes

export CanMac (mac)

/-- The length of a code in bytes. -/
public def macLength := 32

section Constructors

namespace Mac

/-- The constructor of codes: a key and a message. -/
public structure SubF (Bytes : Type) where
  /-- The key. -/
  key : Bytes
  /-- The message. -/
  msg : Bytes

public instance : ALaCarte.FunctorSizeOf SubF where
  sizeOf | {key, msg} => sizeOf key + sizeOf msg

public instance : ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }
  toRepr | {key, msg} => {
    id := ()
    data := ()
    as := #v[key, msg]
  }
  fromRepr
  | {id, data, as} =>
    let key := as[0]
    let msg := as[1]
    { key, msg }
  from_to | {key, msg} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {key, msg} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance : ALaCarte.RepresentableDecidableEq SubF where
public instance : ALaCarte.RepresentableOrd SubF where
public instance : SubBytesFunctor SubF where

/-- Every code has the same length. -/
public def SubF.length [BytesFunctor] : Bytes.PartialLength SubF :=
  fun _ _ => macLength

end Mac

#combine into BytesFunctor, BytesLength from
  Mac,

variable [BytesFunctor] [BytesFunctor.Has SubF]

/-- A code as a term. -/
public abbrev Mac.SubF.pack (x : Mac.SubF Bytes) := BytesView.pack x

public instance : CanMac Bytes where
  mac key msg := ({key, msg} : Mac.SubF Bytes).pack

public theorem mac_inj (key₁ msg₁ key₂ msg₂ : Bytes) :
    mac key₁ msg₁ = mac key₂ msg₂ → key₁ = key₂ ∧ msg₁ = msg₂ := by
  simp only [mac]
  grind

end Constructors

section AttackerKnowledge

/-- The attacker obtains a code by computing it from a key and a message that it knows. -/
public def mac.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] :
    SubAttackerKnowledge SubF where
  pred p out :=
    ∃ key msg,
      out = mac key msg ∧
      p key ∧
      p msg

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  mac,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public theorem attacker_knows_mac (key msg : Bytes) (tr : ExecTrace) :
    key.AttackerKnows tr → msg.AttackerKnows tr → (mac key msg).AttackerKnows tr := by
  intro h_key h_msg
  apply Bytes.AttackerKnows.prove mac.attackerKnowledge
  simp only [mac.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

/-- What a protocol claims with the codes that its honest participants compute: a predicate on
the key, the message and the trace. -/
public class MacPred where
  /-- Whether an honest participant may compute the code of `msg` under `key` on this trace. -/
  pred : [BytesWellFormed] → [GetUsage] → [GetLabel] → Bytes → Bytes → ProofTrace → Prop

/-- The predicate of a protocol's codes keeps holding as the trace grows. -/
public class MacPredProof [BytesInvariants] [MacPred] where
  /-- A claim that holds on a trace holds on every extension of it. -/
  pred_later :
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ key msg tr1 tr2,
      key.WellFormed tr1 →
      msg.WellFormed tr1 →
      tr1 ≤ tr2 →
      MacPred.pred key msg tr1 →
      MacPred.pred key msg tr2

grind_pattern MacPredProof.pred_later => tr1 ≤ tr2, MacPred.pred key msg tr1

/-- A code is as public as its message. It is valid when its key and message are, and when the
protocol's predicate holds of them or the attacker knows the key. -/
public def Mac.invariants [MacPred] : Bytes.PartialInvariants Mac.SubF where
  well_formed := fun {key, msg} rec tr =>
    (rec key) tr ∧ (rec msg) tr
  usage := fun {key, msg} rec tr => Usage.nothing
  label := fun {key, msg} rec tr =>
    (rec msg) tr
  invariant := fun {key, msg} rec tr =>
    (rec key) tr ∧
    (rec msg) tr ∧
    (MacPred.pred key msg tr ∨ (key.label tr).canFlow Label.pub tr.erase)

public theorem Mac.invariantsProofs [BytesInvariants] [MacPred] [MacPredProof] :
    Bytes.PartialInvariantsProofs Mac.invariants where
  invariant_later := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT]
    grind

end Definition

#combine [MacPred] into
  BytesInvariants,
  BytesInvariantsProofs [MacPredProof]
from
  Mac,

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [MacPred]
variable [BytesInvariants] [BytesInvariants.Has invariants]

@[simp]
public theorem mac.WellFormed (key msg : Bytes) (tr : ProofTrace) :
    (mac key msg).WellFormed tr = (key.WellFormed tr ∧ msg.WellFormed tr) := by
  simp [mac, Bytes.WellFormed.eq, Mac.invariants]

@[simp]
public theorem mac.label (key msg : Bytes) (tr : ProofTrace) :
    (mac key msg).label tr = msg.label tr := by
  simp [mac, Bytes.label.eq, Mac.invariants]

@[simp]
public theorem mac.Invariant (key msg : Bytes) (tr : ProofTrace) :
    (mac key msg).Invariant tr =
      (key.Invariant tr ∧ msg.Invariant tr ∧
        (MacPred.pred key msg tr ∨ (key.label tr).canFlow Label.pub tr.erase)) := by
  simp [mac, Bytes.Invariant.eq, Mac.invariants]

/-- A participant may send the code of a public message under a valid key once the protocol's
predicate holds of them. -/
public theorem mac_invariant {key msg : Bytes} {tr : ProofTrace}
    (valid : key.Invariant tr) (sent : msg.Publishable tr) (claim : MacPred.pred key msg tr) :
    (mac key msg).Publishable tr := by
  simp_all [Bytes.Publishable]

/-- A valid code that equals the code of `key` and `msg` carries the protocol's predicate for
them, unless the attacker knows the key. -/
public theorem mac_checked {code key msg : Bytes} {tr : ProofTrace}
    (valid : code.Invariant tr) (same : code = mac key msg) :
    MacPred.pred key msg tr ∨ (key.label tr).canFlow Label.pub tr.erase := by
  subst same
  simp_all

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [MacPred]
variable [BytesInvariants.Has invariants]

public instance : SubAttackerKnowledgeTheorem mac.attackerKnowledge where
  pf := by
    simp only [mac.attackerKnowledge]
    intro out tr h_tr ⟨key, msg, ⟨h_out, h_key, h_msg⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]

end AttackerKnowledgeTheorem

section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [MacPred] [BytesInvariants.Has invariants] into
  SubAttackerKnowledgeTheorem'
from
  mac,

end AttackerKnowledgeTheorem

end Commonware.Symbolic.Mac
