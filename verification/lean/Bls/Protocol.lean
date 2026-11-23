module
public import Bls.Certificate
public import Commonware.Symbolic.Client
public import Commonware.Symbolic.Linear
public import DY.EquationalTheory.Literal
import DY.Meta

/-! The DyLean protocol around the extracted BLS certificate client, in the linear model of
signatures. Members sign subjects and are compromised; the attacker submits any certificate whose
signature it can derive, for a committee whose named keys have derivable proofs of possession;
the client runs the extracted `client_step` and logs what it accepts.

Trusted: `Setup`, `Event`, the steps, their preconditions, the event invariant, the `#combine`
configuration and the theorem statements. The client is the shared `Commonware.Symbolic.accept`
action over the extracted step, so preservation of the trace invariant reduces to
`Certificate.client_step_iff` and `Linear.attribution`. -/

namespace Bls.Protocol
open DY Aeneas Aeneas.Std Commonware.Symbolic Commonware.Symbolic.Linear commonware_symbolic
@[expose] public section

/-- The trusted setup of a client: the keys that the committee registered, in member order, and
the hash that signatures cover. The keys are any keys, so members may register rogue ones; the
hash is any function, so it may collide. -/
class Setup where
  /-- The points that inputs hash to. -/
  Hashed : Type
  /-- The hash that signatures cover. -/
  hash : Input (Slice Std.U8) → Hashed
  /-- The key that every member registered, by index. -/
  keys : List Key
  /-- The number of members fits a `u64`. -/
  bounded : keys.length < 2 ^ 64

/-- What the trace records: a member signs a subject, a member is compromised, and the client
accepts a certificate for a subject with the signer flags it was given. -/
inductive Event where
  /-- A member signs a message in a namespace. -/
  | sign (member : Nat) (ns message : Slice Std.U8)
  /-- A member is compromised. -/
  | compromise (member : Nat)
  /-- The client accepts a certificate for a subject, with the signer flags it was given. -/
  | certify (ns message : Slice Std.U8) (signers : List Bool) (certified : bls.Certified)

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Literal,

#combine +toplevel into ExecEntryT, baseAttackerKnowledge from
  ProtocolEvent Event,

/-- `member` signed `message` in `ns` on the trace. -/
abbrev Signed (tr : ExecTrace) (member : Nat) (ns message : Slice Std.U8) : Prop :=
  tr.EventLogged (Event.sign member ns message)

/-- `member` was compromised on the trace. -/
abbrev Leaked (tr : ExecTrace) (member : Nat) : Prop :=
  tr.EventLogged (Event.compromise member)

noncomputable section

/-- A member signs a subject. -/
def signer (member : Nat) (ns message : Slice Std.U8) : Traceful Unit :=
  ProtocolEvent.logEvent (Event.sign member ns message)

/-- Signing as a step of reachable traces, for any member and subject. -/
def signer.reachability : ReachabilityConfig :=
  .make fun (member, ns, message) => signer member ns message

/-- A member is compromised. -/
def corruption (member : Nat) : Traceful Unit :=
  ProtocolEvent.logEvent (Event.compromise member)

/-- Compromise as a step of reachable traces, for any member. -/
def corruption.reachability : ReachabilityConfig :=
  .make fun member => corruption member

/-- What the attacker submits to the client: a subject, signer flags and a signature. -/
structure Submission [Setup] where
  /-- The namespace of the subject. -/
  ns : Slice Std.U8
  /-- The message of the subject. -/
  message : Slice Std.U8
  /-- The signer flags of the certificate. -/
  signers : Flags
  /-- The signature of the certificate. -/
  signature : Sig Setup.Hashed

/-- The committee that the client trusts. Its own quorum is not asked for: the client applies
its fault model. -/
def roster [Setup] : Roster Key where
  keys := Setup.keys
  quorum := 0#u64
  bounded := Setup.bounded

/-- The extracted client step on a submission, returning the event to log. -/
def decision [Setup] (submission : Submission) : RustM (Option Event) := do
  let certified ← bls.client_step (scheme Setup.hash).terms Roster.committee Flags.signers
    decoded () roster submission.ns submission.message submission.signers
    (some (Point.signature submission.signature))
  RustM.ok (match certified with
    | some certified =>
      some (Event.certify submission.ns submission.message submission.signers.bits certified)
    | none => none)

/-- Run the extracted client step on a submission and log the certificate that it accepts. -/
def client [Setup] (submission : Submission) : Traceful Unit :=
  accept (decision submission)

/-- The attacker submits a signature that it can derive from the signing and compromise events so
far, for flags whose named keys all have a derivable proof of possession. -/
def client.reachability [Setup] : ReachabilityConfig where
  Input := Submission
  PreCond submission tr :=
    Derives Setup.hash (Signed tr) (Leaked tr) submission.signature ∧
    ∀ key ∈ selected submission.signers.bits Setup.keys,
      Derives Setup.hash (Signed tr) (Leaked tr) (term key (Setup.hash (.possession key)))
  step submission := ⟨Unit, client submission⟩

section
variable [Setup]
#combine into ReachabilityConfig from
  signer,
  corruption,
  client,
end

#combine +toplevel into ProofEntryT from
  ProtocolEvent Event,

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Literal,

/-- What an accepted certificate says about the trace before it: its flags span the committee
and name its quorum, the logged event names the committee size and quorum, and every named member
that registered its own key and is not compromised signed exactly the subject, or the hash
collides between something that member's secret was applied to and the subject or the possession
of a named key. -/
def Authentic [Setup] (tr : ExecTrace) (ns message : Slice Std.U8) (signers : List Bool)
    (certified : bls.Certified) : Prop :=
  Setup.keys ≠ [] ∧
  signers.length = Setup.keys.length ∧
  Certificate.quorum Setup.keys.length ≤ signers.count true ∧
  certified.members.val = Setup.keys.length ∧
  certified.quorum.val = Certificate.quorum Setup.keys.length ∧
  ∀ member, signers[member]? = some true → Setup.keys[member]? = some (basis member) →
    ¬ Leaked tr member →
    Signed tr member ns message ∨ ∃ x y, Collision Setup.hash x y ∧
      Origin (Signed tr) member x ∧
      (y = .message ns message ∨ ∃ key ∈ selected signers Setup.keys, y = .possession key)

instance [Setup] : ProtocolEvent.EventInv Event where
  invariant tr event :=
    match event with
    | .certify ns message signers certified => Authentic tr.erase ns message signers certified
    | _ => True

section
variable [Setup]
#combine +toplevel into SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  ProtocolEvent Event,

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Literal,

/-- Every certificate that the extracted client step accepts for a derivable submission is
authentic on the trace it was derived from. -/
theorem decision_sound (submission : Submission) (event : Event)
    (accepted : decision submission = RustM.ok (some event)) (tr : ExecTrace)
    (derived : client.reachability.PreCond submission tr) :
    ∃ certified, event = Event.certify submission.ns submission.message submission.signers.bits
      certified ∧
      Authentic tr submission.ns submission.message submission.signers.bits certified := by
  unfold decision at accepted
  obtain ⟨outcome, run, wrapped⟩ := bind_eq_ok accepted
  obtain ⟨found, ran, accepts, names⟩ := Certificate.client_step_iff (scheme Setup.hash)
    Roster.committee roster Setup.keys 0#u64 (roster.reads) submission.signers
    (some (Point.signature submission.signature)) submission.ns submission.message
  have same : outcome = found := ok_inj (run.symm.trans ran)
  subst same
  cases outcome with
  | none => simpa using ok_inj wrapped
  | some certified =>
    have logged := ok_inj wrapped
    simp at logged
    obtain ⟨members', spans, enough, point, decodes, checks⟩ := accepts.mp rfl
    obtain ⟨members, needed⟩ := names certified rfl
    cases decodes
    have verified := (Point.signature.injEq _ _).mp
      ((check_iff Setup.hash _ submission.ns submission.message _).mp checks)
    rw [sum_eq] at verified
    refine ⟨certified, logged.symm, members', spans, enough, members, needed, ?_⟩
    intro member flag canonical safe
    exact attribution Setup.hash Setup.keys submission.signers.bits member submission.ns
      submission.message submission.signature canonical flag derived.2 derived.1 verified safe

theorem signer_preserves (member : Nat) (ns message : Slice Std.U8) :
    HoareTriple (signer member ns message) (fun _ => True) (fun _ _ => True) := by
  apply HoareTriple.mk
  unfold signer hoareTriple
  intro tr _ inv
  step by trivial
  trivial

theorem corruption_preserves (member : Nat) :
    HoareTriple (corruption member) (fun _ => True) (fun _ _ => True) := by
  apply HoareTriple.mk
  unfold corruption hoareTriple
  intro tr _ inv
  step by trivial
  trivial

theorem client_preserves (submission : Submission) :
    HoareTriple (client submission)
      (fun tr => client.reachability.PreCond submission tr.erase) (fun _ _ => True) :=
  accept_preserves _ _ fun event accepted tr derived => by
    obtain ⟨certified, rfl, authentic⟩ := decision_sound submission event accepted tr.erase derived
    exact authentic

instance : ReachableImpliesInvariant signer.reachability :=
  .mk (fun (member, ns, message) => signer_preserves member ns message)

instance : ReachableImpliesInvariant corruption.reachability :=
  .mk (fun member => corruption_preserves member)

instance : ReachableImpliesInvariant client.reachability :=
  .mk (fun submission => client_preserves submission)

#combine into ReachabilityTheorem from
  signer,
  corruption,
  client,

/-- Every certificate logged on a reachable trace is authentic on the trace before it. -/
theorem certificate_logged (ns message : Slice Std.U8) (signers : List Bool)
    (certified : bls.Certified) (time : Nat) :
    ∀ tr : ExecTrace, tr.Reachable reachability →
      tr.EventLoggedAt (Event.certify ns message signers certified) time →
      Authentic (tr.prefix time) ns message signers certified := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv logged
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged
  simpa [ProtocolEvent.EventInv.invariant] using this

omit [Setup] in
/-- An event on a prefix of the trace is on the trace strictly earlier. -/
theorem earlier {tr : ExecTrace} {time : Nat} {event : Event}
    (logged : (tr.prefix time).EventLogged event) :
    ∃ earlier < time, tr.EventLoggedAt event earlier := by
  obtain ⟨index, there⟩ := logged
  have inside := Trace.EventLoggedAt_implies_i_le_length _ _ _ there
  rw [Trace.prefix_length] at inside
  exact ⟨index, by omega, Trace.EventLoggedAt_le _ _ _ _ (Trace.prefix_le_self ..) there⟩

/-- Authentication of certificates on traces of signing, compromise and extracted client steps.
A certificate logged on a reachable trace has one flag per committee member and names at least
the committee's quorum. Every named member that registered its own key and was not compromised
before the acceptance signed exactly the certificate's namespace and message strictly earlier,
or the hash collides: two different inputs have one point, the first something that the member's
secret was applied to, the second the subject or the possession of a named key. -/
theorem certificate_authentication (ns message : Slice Std.U8) (signers : List Bool)
    (certified : bls.Certified) (time : Nat) (tr : ExecTrace)
    (reachable : tr.Reachable reachability)
    (logged : tr.EventLoggedAt (Event.certify ns message signers certified) time) :
    signers.length = Setup.keys.length ∧
    Certificate.quorum Setup.keys.length ≤ signers.count true ∧
    ∀ member, signers[member]? = some true → Setup.keys[member]? = some (basis member) →
      ¬ Leaked (tr.prefix time) member →
      (∃ earlier < time, tr.EventLoggedAt (Event.sign member ns message) earlier) ∨
      ∃ x y, Collision Setup.hash x y ∧ Origin (Signed (tr.prefix time)) member x ∧
        (y = .message ns message ∨ ∃ key ∈ selected signers Setup.keys, y = .possession key) := by
  obtain ⟨-, spans, enough, -, -, signedBy⟩ :=
    certificate_logged ns message signers certified time tr reachable logged
  refine ⟨spans, enough, fun member flag canonical safe => ?_⟩
  rcases signedBy member flag canonical safe with signed | collision
  · exact Or.inl (earlier signed)
  · exact Or.inr collision

/-- With a hash that has no collisions, every named member that registered its own key and was
not compromised before the acceptance signed exactly the certificate's namespace and message
strictly earlier. -/
theorem collision_free_authentication
    (free : ∀ x y : Input (Slice Std.U8), Setup.hash x = Setup.hash y → x = y)
    (ns message : Slice Std.U8) (signers : List Bool) (certified : bls.Certified) (time : Nat)
    (tr : ExecTrace) (reachable : tr.Reachable reachability)
    (logged : tr.EventLoggedAt (Event.certify ns message signers certified) time) :
    signers.length = Setup.keys.length ∧
    Certificate.quorum Setup.keys.length ≤ signers.count true ∧
    ∀ member, signers[member]? = some true → Setup.keys[member]? = some (basis member) →
      ¬ Leaked (tr.prefix time) member →
      ∃ earlier < time, tr.EventLoggedAt (Event.sign member ns message) earlier := by
  obtain ⟨spans, enough, signedBy⟩ :=
    certificate_authentication ns message signers certified time tr reachable logged
  refine ⟨spans, enough, fun member flag canonical safe => ?_⟩
  rcases signedBy member flag canonical safe with signed | ⟨x, y, clash, -, -⟩
  · exact signed
  · exact absurd (free x y clash.2) clash.1

/-- Two certificates logged on a reachable trace name more common members than the committee
tolerates as faulty. -/
theorem certificates_intersect {ns₁ message₁ ns₂ message₂ : Slice Std.U8}
    {signers₁ signers₂ : List Bool} {certified₁ certified₂ : bls.Certified} {time₁ time₂ : Nat}
    (tr : ExecTrace) (reachable : tr.Reachable reachability)
    (first : tr.EventLoggedAt (Event.certify ns₁ message₁ signers₁ certified₁) time₁)
    (second : tr.EventLoggedAt (Event.certify ns₂ message₂ signers₂ certified₂) time₂) :
    (Setup.keys.length - 1) / 3 < (Certificate.common signers₁ signers₂).length := by
  obtain ⟨members, spans₁, enough₁, -⟩ :=
    certificate_logged ns₁ message₁ signers₁ certified₁ time₁ tr reachable first
  obtain ⟨-, spans₂, enough₂, -⟩ :=
    certificate_logged ns₂ message₂ signers₂ certified₂ time₂ tr reachable second
  exact Certificate.quorum_intersection Setup.keys.length signers₁ signers₂
    (List.length_pos_iff.mpr members) spans₁ spans₂ enough₁ enough₂

/-- Two certificates logged on a reachable trace share a member that signed both subjects, when
the hash has no collisions and all but the tolerated number of members registered their own key
and are never compromised. -/
theorem shared_signer (free : ∀ x y : Input (Slice Std.U8), Setup.hash x = Setup.hash y → x = y)
    (faulty : List Nat) (few : faulty.length ≤ (Setup.keys.length - 1) / 3) (tr : ExecTrace)
    (reachable : tr.Reachable reachability)
    (honest : ∀ member, member ∉ faulty → member < Setup.keys.length →
      Setup.keys[member]? = some (basis member) ∧ ¬ Leaked tr member)
    {ns₁ message₁ ns₂ message₂ : Slice Std.U8} {signers₁ signers₂ : List Bool}
    {certified₁ certified₂ : bls.Certified} {time₁ time₂ : Nat}
    (first : tr.EventLoggedAt (Event.certify ns₁ message₁ signers₁ certified₁) time₁)
    (second : tr.EventLoggedAt (Event.certify ns₂ message₂ signers₂ certified₂) time₂) :
    ∃ member,
      (∃ earlier < time₁, tr.EventLoggedAt (Event.sign member ns₁ message₁) earlier) ∧
      (∃ earlier < time₂, tr.EventLoggedAt (Event.sign member ns₂ message₂) earlier) := by
  obtain ⟨spans₁, -, signed₁⟩ := collision_free_authentication free ns₁ message₁ signers₁
    certified₁ time₁ tr reachable first
  obtain ⟨-, -, signed₂⟩ := collision_free_authentication free ns₂ message₂ signers₂
    certified₂ time₂ tr reachable second
  have many := certificates_intersect tr reachable first second
  have distinct : (Certificate.common signers₁ signers₂).Nodup :=
    (Certificate.namedFrom_sorted _ 0).imp fun order => Nat.ne_of_lt order
  obtain ⟨member, shared, sound⟩ : ∃ member ∈ Certificate.common signers₁ signers₂,
      member ∉ faulty := by
    apply Classical.byContradiction
    intro none
    have inside : Certificate.common signers₁ signers₂ ⊆ faulty := fun member mem =>
      Classical.byContradiction fun out => none ⟨member, mem, out⟩
    have := (List.subperm_of_subset distinct inside).length_le
    omega
  obtain ⟨named₁, named₂⟩ := Certificate.mem_common.mp shared
  have flag₁ : signers₁[member]? = some true := by
    simpa using (Certificate.mem_namedFrom signers₁ 0).mp named₁
  have flag₂ : signers₂[member]? = some true := by
    simpa using (Certificate.mem_namedFrom signers₂ 0).mp named₂
  have inside : member < Setup.keys.length := by
    obtain ⟨bound, -⟩ := List.getElem?_eq_some_iff.mp flag₁
    omega
  obtain ⟨canonical, safe⟩ := honest member sound inside
  have before (time : Nat) : ¬ Leaked (tr.prefix time) member := fun leaked =>
    safe (Trace.EventLogged_le _ _ _ (Trace.prefix_le_self ..) leaked)
  exact ⟨member, signed₁ member flag₁ canonical (before time₁),
    signed₂ member flag₂ canonical (before time₂)⟩

/-- A signing quorum can be certified. After the named members, each with its own key registered,
have signed a subject, the attacker can derive their combined signature and the proofs of
possession, and the extracted client step accepts the certificate with their flags. -/
theorem honest_certificate (tr : ExecTrace) (ns message : Slice Std.U8) (signers : Flags)
    (members : Setup.keys ≠ []) (spans : signers.bits.length = Setup.keys.length)
    (enough : Certificate.quorum Setup.keys.length ≤ signers.bits.count true)
    (honest : ∀ member, signers.bits[member]? = some true →
      Setup.keys[member]? = some (basis member) ∧ Signed tr member ns message) :
    client.reachability.PreCond
        ⟨ns, message, signers,
          term (total (selected signers.bits Setup.keys)) (Setup.hash (.message ns message))⟩ tr ∧
      ∃ certified, decision
        ⟨ns, message, signers,
          term (total (selected signers.bits Setup.keys)) (Setup.hash (.message ns message))⟩ =
        RustM.ok (some (Event.certify ns message signers.bits certified)) := by
  have own : ∀ key ∈ selected signers.bits Setup.keys,
      ∃ member, key = basis member ∧ Signed tr member ns message := by
    intro key mem
    obtain ⟨member, held, flag⟩ := of_mem_selected signers.bits Setup.keys mem
    obtain ⟨canonical, signed⟩ := honest member flag
    exact ⟨member, Option.some.inj (held.symm.trans canonical), signed⟩
  refine ⟨⟨derives_total _ _ fun key mem => ?_, fun key mem => ?_⟩, ?_⟩
  · obtain ⟨member, rfl, signed⟩ := own key mem
    exact Derives.sign signed
  · obtain ⟨member, rfl, -⟩ := own key mem
    exact Derives.pop member
  · obtain ⟨found, ran, accepts, -⟩ := Certificate.client_step_iff (scheme Setup.hash)
      Roster.committee roster Setup.keys 0#u64 (roster.reads) signers
      (some (Point.signature (term (total (selected signers.bits Setup.keys))
        (Setup.hash (.message ns message))))) ns message
    have accepted : found.isSome := accepts.mpr ⟨members, spans, enough, _, rfl, by
      rw [check_iff, sum_eq]⟩
    obtain ⟨certified, rfl⟩ := Option.isSome_iff_exists.mp accepted
    exact ⟨certified, by simp [decision, ran]⟩
end

end
end
end Bls.Protocol
