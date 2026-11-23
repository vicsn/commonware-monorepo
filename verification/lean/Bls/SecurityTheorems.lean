module
public import Bls.Protocol

/-! The statements of the BLS certificate target. The first four hold for any signature scheme
and speak about the extracted client step alone. The rest hold in the linear model, on traces of
signing, compromise and extracted client steps. -/

namespace Bls
open DY Aeneas Aeneas.Std Commonware.Symbolic Commonware.Symbolic.Linear commonware_symbolic
@[expose] public section

variable {K P : Type}

/-- The extracted client step returns on every certificate, whatever the scheme does. -/
theorem client_total (S : Signing K P) (roster : Roster K) (flags : Flags) (signature : Option P)
    (ns message : Slice Std.U8) :
    ∃ event, bls.client_step S.terms Roster.committee Flags.signers decoded () roster ns message
      flags signature = RustM.ok event := by
  obtain ⟨event, ran, -⟩ := Certificate.client_step_iff S Roster.committee roster roster.keys
    roster.quorum roster.reads flags signature ns message
  exact ⟨event, ran⟩

/-- What the extracted client step has checked when it accepts. -/
theorem client_accepts (S : Signing K P) (roster : Roster K) (flags : Flags) (signature : Option P)
    (ns message : Slice Std.U8) (certified : bls.Certified)
    (accepted : bls.client_step S.terms Roster.committee Flags.signers decoded () roster ns message
      flags signature = RustM.ok (some certified)) :
    Certificate.Accepts S roster.keys flags.bits signature ns message ∧
      certified.members.val = roster.keys.length ∧
      certified.quorum.val = Certificate.quorum roster.keys.length := by
  obtain ⟨event, ran, accepts, names⟩ := Certificate.client_step_iff S Roster.committee roster
    roster.keys roster.quorum roster.reads flags signature ns message
  have same : event = some certified := ok_inj (ran.symm.trans accepted)
  subst same
  exact ⟨accepts.mp rfl, names certified rfl⟩

/-- Signer-index interpretation. An accepted certificate has one flag per member of the committee.
Its signature is checked under the keys of exactly the members whose flags are set: each member
once, in index order, and member `index` by the key registered at `index`. -/
theorem signer_index_interpretation (S : Signing K P) (roster : Roster K) (flags : Flags)
    (signature : Option P) (ns message : Slice Std.U8) (certified : bls.Certified)
    (accepted : bls.client_step S.terms Roster.committee Flags.signers decoded () roster ns message
      flags signature = RustM.ok (some certified)) :
    flags.bits.length = roster.keys.length ∧ certified.members.val = roster.keys.length ∧
      selected flags.bits roster.keys =
        (named flags.bits).filterMap (fun index => roster.keys[index]?) ∧
      (named flags.bits).Pairwise (· < ·) ∧
      ∀ index, index ∈ named flags.bits ↔ flags.bits[index]? = some true := by
  obtain ⟨holds, members, -⟩ :=
    client_accepts S roster flags signature ns message certified accepted
  obtain ⟨spans, selects, ascending, exactly⟩ := Certificate.signer_index_interpretation holds
  exact ⟨spans, members, selects, ascending, exactly⟩

/-- Quorum authorization. An accepted certificate names at least the `N3f1` quorum of the
committee: all but the faults it tolerates. The named indices are members, and none is named
twice. -/
theorem quorum_authorization (S : Signing K P) (roster : Roster K) (flags : Flags)
    (signature : Option P) (ns message : Slice Std.U8) (certified : bls.Certified)
    (accepted : bls.client_step S.terms Roster.committee Flags.signers decoded () roster ns message
      flags signature = RustM.ok (some certified)) :
    certified.quorum.val = Certificate.quorum roster.keys.length ∧
      Certificate.quorum roster.keys.length ≤ (named flags.bits).length ∧
      (named flags.bits).Nodup ∧ ∀ index ∈ named flags.bits, index < roster.keys.length := by
  obtain ⟨holds, -, needed⟩ := client_accepts S roster flags signature ns message certified accepted
  obtain ⟨enough, distinct, inside⟩ := Certificate.quorum_authorization holds
  exact ⟨needed, enough, distinct, inside⟩

/-- Subject binding. The signature of an accepted certificate decodes and signs the hash of
exactly the namespace and message that the client was asked about, under the sum of the keys of
the named members. -/
theorem subject_binding (S : Signing K P) (roster : Roster K) (flags : Flags)
    (signature : Option P) (ns message : Slice Std.U8) (certified : bls.Certified)
    (accepted : bls.client_step S.terms Roster.committee Flags.signers decoded () roster ns message
      flags signature = RustM.ok (some certified)) :
    ∃ point, signature = some point ∧
      S.check (S.sum (selected flags.bits roster.keys)) (S.hash ns message) point = true :=
  Certificate.subject_binding
    (client_accepts S roster flags signature ns message certified accepted).1

/-- Authentication of certificates on traces of signing, compromise and extracted client steps,
for any registered keys and any hash. A logged certificate has one flag per member and names the
committee's quorum. Every named member that registered its own key and was not compromised
before the acceptance signed exactly the certificate's namespace and message strictly earlier,
or the hash collides between something that member's secret was applied to and the subject or
the possession of a named key. -/
theorem certificate_authentication [Protocol.Setup] (ns message : Slice Std.U8)
    (signers : List Bool) (certified : bls.Certified) (time : Nat) (tr : ExecTrace)
    (reachable : tr.Reachable Protocol.reachability)
    (logged : tr.EventLoggedAt (Protocol.Event.certify ns message signers certified) time) :
    signers.length = Protocol.Setup.keys.length ∧
    Certificate.quorum Protocol.Setup.keys.length ≤ signers.count true ∧
    ∀ member, signers[member]? = some true →
      Protocol.Setup.keys[member]? = some (basis member) →
      ¬ Protocol.Leaked (tr.prefix time) member →
      (∃ earlier < time, tr.EventLoggedAt (Protocol.Event.sign member ns message) earlier) ∨
      ∃ x y, Collision Protocol.Setup.hash x y ∧
        Origin (Protocol.Signed (tr.prefix time)) member x ∧
        (y = .message ns message ∨
          ∃ key ∈ selected signers Protocol.Setup.keys, y = .possession key) :=
  Protocol.certificate_authentication ns message signers certified time tr reachable logged

/-- Authentication with a hash that has no collisions: every named member that registered its own
key and was not compromised before the acceptance signed exactly the certificate's namespace and
message strictly earlier. -/
theorem collision_free_certificate_authentication [Protocol.Setup]
    (free : ∀ x y : Input (Slice Std.U8),
      Protocol.Setup.hash x = Protocol.Setup.hash y → x = y)
    (ns message : Slice Std.U8) (signers : List Bool) (certified : bls.Certified) (time : Nat)
    (tr : ExecTrace) (reachable : tr.Reachable Protocol.reachability)
    (logged : tr.EventLoggedAt (Protocol.Event.certify ns message signers certified) time) :
    signers.length = Protocol.Setup.keys.length ∧
    Certificate.quorum Protocol.Setup.keys.length ≤ signers.count true ∧
    ∀ member, signers[member]? = some true →
      Protocol.Setup.keys[member]? = some (basis member) →
      ¬ Protocol.Leaked (tr.prefix time) member →
      ∃ earlier < time, tr.EventLoggedAt (Protocol.Event.sign member ns message) earlier :=
  Protocol.collision_free_authentication free ns message signers certified time tr reachable logged

/-- Two certificates logged on one reachable trace share a member that signed both subjects, when
the hash has no collisions and all but the tolerated number of members registered their own key
and are never compromised. -/
theorem certificates_share_a_signer [Protocol.Setup]
    (free : ∀ x y : Input (Slice Std.U8),
      Protocol.Setup.hash x = Protocol.Setup.hash y → x = y)
    (faulty : List Nat) (few : faulty.length ≤ (Protocol.Setup.keys.length - 1) / 3)
    (tr : ExecTrace) (reachable : tr.Reachable Protocol.reachability)
    (honest : ∀ member, member ∉ faulty → member < Protocol.Setup.keys.length →
      Protocol.Setup.keys[member]? = some (basis member) ∧ ¬ Protocol.Leaked tr member)
    {ns₁ message₁ ns₂ message₂ : Slice Std.U8} {signers₁ signers₂ : List Bool}
    {certified₁ certified₂ : bls.Certified} {time₁ time₂ : Nat}
    (first : tr.EventLoggedAt (Protocol.Event.certify ns₁ message₁ signers₁ certified₁) time₁)
    (second : tr.EventLoggedAt (Protocol.Event.certify ns₂ message₂ signers₂ certified₂) time₂) :
    ∃ member,
      (∃ earlier < time₁, tr.EventLoggedAt (Protocol.Event.sign member ns₁ message₁) earlier) ∧
      (∃ earlier < time₂, tr.EventLoggedAt (Protocol.Event.sign member ns₂ message₂) earlier) :=
  Protocol.shared_signer free faulty few tr reachable honest first second

end
end Bls
