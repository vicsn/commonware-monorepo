module
public import Sake.Owner
public import Sake.Steps
import DY.Meta

/-! The invariant that every reachable trace of the SAKE protocol satisfies. Checked.

An identity key signs only two kinds of transcript: the one a dialer signs once it has logged
that it started, and the one a listener signs once it has logged that it answered. The two are
told apart by `Opening.signed_ne`. A peer that verifies a signature therefore finds the matching
event of the key's owner on the trace, unless that identity key is compromised. The signature
also says that the signed ephemeral key belongs to a secret that only a compromise of what its
owner keeps reveals, which is what makes the shared secret, and with it the secret transcript,
secret.

A confirmation is a message authentication code under the hash of the secret transcript. The
dialer's confirmation is computed only by a dialer that has logged that it finished the exchange
with that transcript, so a listener that checks it finds that event, unless the attacker knows
the transcript. The listener's confirmation carries no claim: its signature already binds it.

The event invariant records these facts for the events that finish a handshake, and each action
is shown to preserve the invariant over the extracted step it runs. -/

namespace Sake
open DY DY.Comparse Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-! ## Messages and secrets -/

theorem SynMessage.IsWellFormed_eq
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x : SynMessage) (tr : τ) :
    IsWellFormed pre x tr = (pre x.epk tr ∧ pre x.sig tr) := by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern SynMessage.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] SynMessage.IsWellFormed_eq => IsWellFormed pre x tr

theorem SynAckMessage.IsWellFormed_eq
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x : SynAckMessage) (tr : τ) :
    IsWellFormed pre x tr = (pre x.epk tr ∧ pre x.sig tr ∧ pre x.confirmation tr) := by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern SynAckMessage.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] SynAckMessage.IsWellFormed_eq => IsWellFormed pre x tr

theorem DialerSecret.IsWellFormed_eq
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x : DialerSecret) (tr : τ) :
    IsWellFormed pre x tr = (pre x.epk tr ∧ pre x.esk tr) := by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern DialerSecret.IsWellFormed_eq => IsWellFormed pre x tr

theorem ListenerSecret.IsWellFormed_eq
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x : ListenerSecret) (tr : τ) :
    IsWellFormed pre x tr = (pre x.epk tr ∧ pre x.transcript tr) := by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ListenerSecret.IsWellFormed_eq => IsWellFormed pre x tr

/-! ## What terms and entries must satisfy -/

#combine +toplevel into ProofEntryT from
  Network,
  Random,
  ProtocolEvent Event,
  PersistentLocalState.State Dialing,
  PersistentLocalState.State Listening,
  PersistentLocalState.CompromisableState DialerSecret,
  PersistentLocalState.CompromisableState ListenerSecret,
  LongTermKeys "SAKE PKI",

theorem DialerCompromised_le (dialer : Participant) (epk : Bytes) (tr1 tr2 : ExecTrace) :
    tr1 ≤ tr2 → DialerCompromised dialer epk tr1 → DialerCompromised dialer epk tr2 := by
  simp only [DialerCompromised]
  grind

grind_pattern DialerCompromised_le => tr1 ≤ tr2, DialerCompromised dialer epk tr1

theorem ListenerCompromised_le (listener : Participant) (epk : Bytes) (tr1 tr2 : ExecTrace) :
    tr1 ≤ tr2 → ListenerCompromised listener epk tr1 → ListenerCompromised listener epk tr2 := by
  simp only [ListenerCompromised]
  grind

grind_pattern ListenerCompromised_le => tr1 ≤ tr2, ListenerCompromised listener epk tr1

/-- Who may know the ephemeral secret of a dialer: nobody, until the attacker compromises what
the dialer keeps for its ephemeral key. -/
def dialerSecrecy (dialer : Participant) (epk : Bytes) : Label where
  isCorrupt tr := DialerCompromised dialer epk tr

/-- Who may know the ephemeral secret of a listener: nobody, until the attacker compromises what
the listener keeps for its ephemeral key. -/
def listenerSecrecy (listener : Participant) (epk : Bytes) : Label where
  isCorrupt tr := ListenerCompromised listener epk tr

/-- Who may know the secret transcript of an exchange: whoever compromises what either peer
keeps for it. -/
def exchangeSecrecy (dialer listener : Participant) (exchange : Exchange) : Label :=
  (dialerSecrecy dialer exchange.dialerKey).join (listenerSecrecy listener exchange.listenerKey)

/-- The owner of an identity key, as the data of its usage. -/
structure Owner where
  /-- The participant that owns the key. -/
  principal : Participant

instance : ParseableSerializeable Owner := .make <|
  .triviallyIsomorphic
    (.string)
    (fun principal => { principal })
    (fun { principal := principal } => principal)

/-- The usage of the identity key of a participant. -/
@[grind]
def identityUsage (owner : Participant) : Usage := {
  type := "SigKey",
  tag := "SAKE PKI",
  data := serialize ({ principal := owner } : Owner)
}

@[grind inj]
theorem identityUsage_inj : Function.Injective identityUsage := by
  simp [Function.Injective, identityUsage]
  grind

/-- What an identity key signs: the opening of a dialer that logged its start, or the exchange
of a listener that logged its answer with the secret transcript that its ephemeral key gives.
Either way the signed ephemeral key belongs to a secret that only a compromise of what the
signer keeps reveals. -/
instance signPred : Signature.SignPred where
  pred usage _ msg tr :=
    (∃ dialer opening secret,
      usage = identityUsage dialer ∧
      msg = Hash.hash opening.signed ∧
      opening.dialerKey = DiffieHellman.dhPk secret ∧
      secret.label tr = dialerSecrecy dialer opening.dialerKey ∧
      tr.erase.EventLogged (Event.dialStart dialer opening)) ∨
    (∃ listener exchange secret,
      usage = identityUsage listener ∧
      msg = Hash.hash exchange.signed ∧
      exchange.listenerKey = DiffieHellman.dhPk secret ∧
      secret.label tr = listenerSecrecy listener exchange.listenerKey ∧
      tr.erase.EventLogged (Event.listenStart listener exchange
        (Concat.concat exchange.signed (DiffieHellman.dh exchange.dialerKey secret))))

instance
    [BytesInvariants]
    [BytesInvariants.Has DiffieHellman.DhPk.invariants]
    [BytesInvariants.Has Literal.invariants]
    [BytesInvariants.Has Concat.invariants]
    [BytesInvariants.Has Hash.invariants] :
    Signature.SignPredProof where
  pred_later := by
    intro _ _ _ _ _ _ tr1 tr2 _ wf _ signed
    rcases signed with ⟨dialer, opening, secret, usage, rfl, key, label, logged⟩ |
      ⟨listener, exchange, secret, usage, rfl, key, label, logged⟩
    · refine Or.inl ⟨dialer, opening, secret, usage, rfl, key, ?_, by grind⟩
      simp only [Hash.hash.WellFormed, Opening.signed, Concat.concat.WellFormed, key,
        DiffieHellman.dhPk.WellFormed] at wf
      grind
    · refine Or.inr ⟨listener, exchange, secret, usage, rfl, key, ?_, by grind⟩
      simp only [Hash.hash.WellFormed, Exchange.signed, Concat.concat.WellFormed, key,
        DiffieHellman.dhPk.WellFormed] at wf
      grind

/-- What a confirmation claims. The listener's confirmation claims nothing. The dialer's
confirmation is the code of its label under the hash of a secret transcript, and it claims that
a dialer logged that it finished the exchange with that transcript. -/
instance macPred : Mac.MacPred where
  pred key msg tr :=
    msg = Literal.literalToBytes (toByteArray listenerLabel) ∨
    (∃ dialer listener exchange shared,
      key = Hash.hash (Concat.concat exchange.signed shared) ∧
      msg = Literal.literalToBytes (toByteArray dialerLabel) ∧
      tr.erase.EventLogged (Event.dialFinish dialer listener exchange
        (Concat.concat exchange.signed shared)))

instance [BytesInvariants] : Mac.MacPredProof where
  pred_later := by
    intro _ _ _ _ _ _ _ _ _ _ claim
    rcases claim with listener | ⟨dialer, listener, exchange, shared, h⟩
    · exact Or.inl listener
    · exact Or.inr ⟨dialer, listener, exchange, shared, by grind⟩

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,
  Mac,

@[grind]
instance : LongTermKeys.ProofConfig "SAKE PKI" identityUsage (LongTermKeys.label "SAKE PKI") where
  IsLongTermPublicKey who vk tr :=
    vk.Publishable tr ∧
    vk.signkeyLabel tr = LongTermKeys.label "SAKE PKI" who vk ∧
    vk.SignkeyHasUsage (identityUsage who) tr
  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

/-- The secret part of what a dialer keeps is the secret of its ephemeral key, which only a
compromise of this part reveals. -/
instance dialerSecretInv : PersistentLocalState.CompromisableLocalStateInv DialerSecret where
  invariant me kept tr :=
    kept.epk = DiffieHellman.dhPk kept.esk ∧
    kept.epk.Publishable tr ∧
    kept.esk.Invariant tr ∧
    kept.esk.label tr = dialerSecrecy me kept.epk
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have : (dialerSecrecy participant state.epk).canFlow
        (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, dialerSecrecy, DialerCompromised]
      grind
    grind [canFlowTrans]

/-- The secret part of what a listener keeps is a transcript that a compromise of this part may
reveal. -/
instance listenerSecretInv : PersistentLocalState.CompromisableLocalStateInv ListenerSecret where
  invariant me kept tr :=
    kept.epk.Publishable tr ∧
    kept.transcript.Invariant tr ∧
    (kept.transcript.label tr).canFlow (listenerSecrecy me kept.epk) tr.erase
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have : (listenerSecrecy participant state.epk).canFlow
        (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, listenerSecrecy, ListenerCompromised]
      grind
    grind [canFlowTrans]

/-- What a dialer keeps is the secret of its ephemeral key and the transcript of the opening
that it logged, for a listener whose identity key it looked up. -/
instance dialingInv : PersistentLocalState.LocalStateInv Dialing where
  invariant me kept tr :=
    kept.secret.Invariant tr ∧
    kept.secret.label tr = dialerSecrecy me kept.opening.dialerKey ∧
    kept.opening.dialerKey = DiffieHellman.dhPk kept.secret ∧
    kept.transcript = kept.opening.signed ∧
    kept.transcript.Publishable tr ∧
    LongTermKeys.IsLongTermPublicKey "SAKE PKI" kept.listener kept.opening.listener tr ∧
    tr.erase.EventLogged (Event.dialStart me kept.opening)
  invariant_later := by grind

/-- A listener keeps the secret transcript of its exchange, which names its own identity key.
Unless the identity key of the dialer it looked up is compromised, that dialer started the
opening, and only a compromise of what either peer keeps reveals the transcript. -/
instance listeningInv : PersistentLocalState.LocalStateInv Listening where
  invariant me kept tr :=
    kept.transcript.Invariant tr ∧
    (∃ shared, kept.transcript = Concat.concat kept.exchange.signed shared) ∧
    (∃ key, kept.exchange.listener = Signature.vk key ∧
      LongTermKeys.IsLongTermSecretKey "SAKE PKI" me key tr) ∧
    ((tr.erase.EventLogged (Event.dialStart kept.dialer kept.exchange.toOpening) ∧
        (exchangeSecrecy kept.dialer me kept.exchange).canFlow (kept.transcript.label tr)
          tr.erase) ∨
      (LongTermKeys.label "SAKE PKI" kept.dialer kept.exchange.dialer).isCorrupt tr.erase)
  invariant_later := by
    intro me kept tr1 tr2 later ⟨valid, shared, ⟨key, identity, owned⟩, authentic⟩
    exact ⟨by grind, shared,
      ⟨key, identity, LongTermKeys.IsLongTermSecretKey_later "SAKE PKI" me key tr1 tr2 later owned⟩,
      by grind⟩

/-- A dialer starts only under its own identity key. A dialer finishes only an exchange whose
opening it started, whose listener identity key it looked up under the listener's name, and
that this listener answered with the same secret transcript, which only a compromise of what
either peer keeps reveals. A listener finishes only an exchange
whose opening the dialer it looked up started, whose transcript is secret in the same way, and
that this dialer finished with the same transcript unless what either peer keeps is
compromised. Each of these holds unless the identity key of the peer is compromised. No peer
finishes an exchange that it has finished before. -/
instance eventInv : ProtocolEvent.EventInv Event where
  invariant tr event :=
    match event with
    | .dialStart dialer opening =>
      ∃ key, opening.dialer = Signature.vk key ∧
        LongTermKeys.IsLongTermSecretKey "SAKE PKI" dialer key tr
    | .listenStart _ _ _ => True
    | .dialFinish dialer listener exchange secret =>
      ¬ tr.erase.EventLogged (Event.dialFinish dialer listener exchange secret) ∧
      tr.erase.EventLogged (Event.dialStart dialer exchange.toOpening) ∧
      LongTermKeys.IsLongTermPublicKey "SAKE PKI" listener exchange.listener tr ∧
      ((tr.erase.EventLogged (Event.listenStart listener exchange secret) ∧
          secret.Invariant tr ∧
          (exchangeSecrecy dialer listener exchange).canFlow (secret.label tr) tr.erase) ∨
        (LongTermKeys.label "SAKE PKI" listener exchange.listener).isCorrupt tr.erase)
    | .listenFinish listener dialer exchange secret =>
      ¬ tr.erase.EventLogged (Event.listenFinish listener dialer exchange secret) ∧
      ((tr.erase.EventLogged (Event.dialStart dialer exchange.toOpening) ∧
          secret.Invariant tr ∧
          (exchangeSecrecy dialer listener exchange).canFlow (secret.label tr) tr.erase ∧
          (tr.erase.EventLogged (Event.dialFinish dialer listener exchange secret) ∨
            (exchangeSecrecy dialer listener exchange).isCorrupt tr.erase)) ∨
        (LongTermKeys.label "SAKE PKI" dialer exchange.dialer).isCorrupt tr.erase)

#combine +toplevel into SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  Network,
  Random,
  ProtocolEvent Event,
  PersistentLocalState.State Dialing,
  PersistentLocalState.State Listening,
  PersistentLocalState.CompromisableState DialerSecret,
  PersistentLocalState.CompromisableState ListenerSecret,
  LongTermKeys "SAKE PKI",

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,
  Mac,

/-! ## Terms that may be sent -/

theorem stamp_publishable (time : Std.U64) (tr : ProofTrace) : (stamp time).Publishable tr := by
  simp only [stamp]
  grind [Literal.literalToBytes.Invariant, Literal.literalToBytes.label]

theorem start_publishable (ns : ByteArray) (tr : ProofTrace) : (start ns).Publishable tr := by
  simp only [start]
  grind [Hash.hash.Invariant, Hash.hash.label, Literal.literalToBytes.Invariant,
    Literal.literalToBytes.label]

theorem label_publishable (label : Slice Std.U8) (tr : ProofTrace) :
    (Literal.literalToBytes (toByteArray label) : Bytes).Publishable tr := by
  grind [Literal.literalToBytes.Invariant, Literal.literalToBytes.label]

theorem concat_publishable {a b : Bytes} {tr : ProofTrace}
    (left : a.Publishable tr) (right : b.Publishable tr) :
    (Concat.concat a b).Publishable tr := by
  grind [Concat.concat.Invariant, Concat.concat.label]

theorem hash_publishable {a : Bytes} {tr : ProofTrace} (input : a.Publishable tr) :
    (Hash.hash a).Publishable tr := by
  grind [Hash.hash.Invariant, Hash.hash.label]

theorem dhPk_publishable {secret : Bytes} {tr : ProofTrace} (valid : secret.Invariant tr) :
    (DiffieHellman.dhPk secret).Publishable tr := by
  grind [DiffieHellman.dhPk.Invariant, DiffieHellman.dhPk.label]

theorem vk_publishable {key : Bytes} {tr : ProofTrace} (valid : key.Invariant tr) :
    (Signature.vk key).Publishable tr := by
  grind [Signature.vk.Invariant, Signature.vk.label]

theorem Opening.signed_publishable {o : Opening} {tr : ProofTrace}
    (dialer : o.dialer.Publishable tr) (listener : o.listener.Publishable tr)
    (key : o.dialerKey.Publishable tr) : o.signed.Publishable tr :=
  concat_publishable (concat_publishable (concat_publishable (concat_publishable
    (start_publishable _ _) (stamp_publishable _ _)) listener) dialer) key

theorem Exchange.signed_publishable {e : Exchange} {tr : ProofTrace}
    (opening : e.toOpening.signed.Publishable tr) (key : e.listenerKey.Publishable tr) :
    e.signed.Publishable tr :=
  concat_publishable (concat_publishable opening (stamp_publishable _ _)) key

/-- The secret transcript of an exchange is a valid term when the peer's ephemeral key came
from the network and the local ephemeral secret is valid. -/
theorem agreed_invariant {signed key secret : Bytes} {tr : ProofTrace}
    (transcript : signed.Publishable tr) (peer : key.Publishable tr)
    (own : secret.Invariant tr) :
    (Concat.concat signed (DiffieHellman.dh key secret)).Invariant tr := by
  have shared := DiffieHellman.dh.Invariant key secret tr ⟨by grind, own⟩
  grind [Concat.concat.Invariant]

/-- Only whoever may know one of the two ephemeral secrets may know the secret transcript. -/
theorem agreed_secrecy {signed theirs ours : Bytes} {tr : ProofTrace} :
    ((theirs.label tr).join (ours.label tr)).canFlow
      ((Concat.concat signed (DiffieHellman.dh (DiffieHellman.dhPk theirs) ours)).label tr)
      tr.erase := by
  simp only [Concat.concat.label, DiffieHellman.dh.label, Bytes.dhSkLabel_dhPk]
  grind [Label.canFlow]

/-- Whoever may know the local ephemeral secret may know the secret transcript. -/
theorem agreed_known {signed key ours : Bytes} {tr : ProofTrace}
    (sent : signed.Publishable tr) :
    ((Concat.concat signed (DiffieHellman.dh key ours)).label tr).canFlow
      (ours.label tr) tr.erase := by
  simp only [Concat.concat.label, DiffieHellman.dh.label]
  grind [Label.canFlow]

theorem join_comm_canFlow {a b c : Label} {tr : ExecTrace} (h : (a.join b).canFlow c tr) :
    (b.join a).canFlow c tr := by
  grind [Label.canFlow]

/-- The listener's confirmation of a valid transcript may be sent. -/
theorem listener_confirmation_publishable {transcript : Bytes} {tr : ProofTrace}
    (valid : transcript.Invariant tr) :
    (confirmation transcript listenerLabel).Publishable tr := by
  simp only [confirmation]
  refine Mac.mac_invariant (by grind [Hash.hash.Invariant]) (label_publishable _ _) ?_
  simp only [Mac.MacPred.pred]
  exact Or.inl (by trivial)

/-- The dialer's confirmation of a valid transcript may be sent once the dialer has logged that
it finished the exchange with that transcript. -/
theorem dialer_confirmation_publishable {dialer listener : Participant} {exchange : Exchange}
    {shared : Bytes} {tr : ProofTrace}
    (valid : (Concat.concat exchange.signed shared).Invariant tr)
    (finished : tr.erase.EventLogged (Event.dialFinish dialer listener exchange
      (Concat.concat exchange.signed shared))) :
    (confirmation (Concat.concat exchange.signed shared) dialerLabel).Publishable tr := by
  simp only [confirmation]
  refine Mac.mac_invariant (by grind [Hash.hash.Invariant]) (label_publishable _ _) ?_
  simp only [Mac.MacPred.pred]
  exact Or.inr ⟨dialer, listener, exchange, shared, by trivial, by trivial, finished⟩

/-! ## Every action preserves the invariant -/

attribute [local grind] ProtocolEvent.EventInv.invariant
attribute [local grind] eventInv
attribute [local grind] Signature.SignPred.pred
attribute [local grind] signPred
attribute [local grind] PersistentLocalState.LocalStateInv.invariant
attribute [local grind] PersistentLocalState.CompromisableLocalStateInv.toLocalStateInv
attribute [local grind] dialingInv
attribute [local grind] listeningInv
attribute [local grind] dialerSecretInv
attribute [local grind] listenerSecretInv
attribute [local grind] LongTermKeys.IsLongTermPublicKey
attribute [local grind] LongTermKeys.IsLongTermSecretKey

theorem firstTime_run {event : Event} {tr : ExecTrace} (unlogged : ¬ tr.EventLogged event) :
    (firstTime event).run tr = (some (), ⟨tr, Trace.le_refl tr⟩) := by
  simp only [firstTime]
  rw [Traceful.run_mk]
  simp [unlogged]

theorem firstTime_run_logged {event : Event} {tr : ExecTrace} (logged : tr.EventLogged event) :
    (firstTime event).run tr = (none, ⟨tr, Trace.le_refl tr⟩) := by
  simp only [firstTime]
  rw [Traceful.run_mk]
  simp [logged]

/-- What follows `firstTime` runs only on a trace that has not logged the event. -/
theorem firstTime_then {α : Type} {event : Event} {next : Traceful α}
    {post : α → ProofTrace → Prop} {tr : ProofTrace} (inv : tr.Invariant)
    (rest : ¬ tr.erase.EventLogged event → wp next post tr) :
    wp (firstTime event >>= fun _ => next) post tr := by
  by_cases logged : tr.erase.EventLogged event
  · simp only [wp]
    rw [Traceful.run_bind, firstTime_run_logged logged]
    exact ⟨tr, trivial, inv, rfl, Trace.le_refl tr⟩
  · have := rest logged
    simp only [wp] at this ⊢
    rw [Traceful.run_bind, firstTime_run logged]
    exact this

@[instance]
theorem dial.proof (me listener : Participant) (skHandle pkHandle : Nat) (ns : ByteArray)
    (now : Std.U64) (window : sake.Window) :
    HoareTriple (dial me listener skHandle pkHandle ns now window)
      (fun _ => True) (fun _ _ => True) := by
  unfold dial
  step
  step
  step with ⟨fun secret => dialerSecrecy me (DiffieHellman.dhPk secret), Usage.nothing⟩
  step with ⟨fun _ => Label.secret, Usage.nothing⟩
  rw [dial_start_eq, run_ok]
  simp only [pure_bind]
  set opening : Opening :=
    { ns, dialer := Signature.vk key, listener := listenerKey, dialed := now,
      dialerKey := DiffieHellman.dhPk drawn } with opening_eq
  step by
    simp only [ProtocolEvent.EventInv.invariant]
    exact ⟨key, rfl, by assumption⟩
  have signed : opening.signed.Publishable tr :=
    Opening.signed_publishable (vk_publishable (by grind)) (by grind) (dhPk_publishable (by grind))
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    have ephemeral := dhPk_publishable (tr := tr) (secret := drawn) (by grind)
    grind
  step by
    have pred : Signature.SignPred.pred (identityUsage me) (Signature.vk key)
        (Hash.hash opening.signed) tr := by
      simp only [Signature.SignPred.pred]
      exact Or.inl ⟨me, opening, drawn, rfl, rfl, rfl, by assumption, by assumption⟩
    have valid : (Signature.sign key nonce (Hash.hash opening.signed)).Publishable tr := by
      have hashed : (Hash.hash opening.signed).Publishable tr := hash_publishable (by grind)
      have := Signature.sign.Invariant key nonce _ (identityUsage me) tr
        ⟨by grind, by grind, by grind, by grind, by grind, Or.inl ⟨rfl, pred⟩⟩
      grind [Signature.sign.label]
    have epk := dhPk_publishable (tr := tr) (secret := drawn) (by grind)
    grind
  step
  grind

@[instance]
theorem listen.proof (me dialer : Participant) (skHandle pkHandle msgHandle : Nat)
    (ns : ByteArray) (now : Std.U64) (window : sake.Window) (dialed : Std.U64) :
    HoareTriple (listen me dialer skHandle pkHandle msgHandle ns now window dialed)
      (fun _ => True) (fun _ _ => True) := by
  unfold listen
  step
  step
  step
  step
  step with ⟨fun secret => listenerSecrecy me (DiffieHellman.dhPk secret), Usage.nothing⟩
  step with ⟨fun _ => Label.secret, Usage.nothing⟩
  rw [listen_start_eq, run_ok]
  simp only [pure_bind]
  split_ifs with inside verified
  · simp only []
    set exchange : Exchange :=
      { ns, dialer := dialerKey, listener := Signature.vk key, dialed, dialerKey := msg.epk,
        answered := now, listenerKey := DiffieHellman.dhPk drawn } with exchange_eq
    have epk : msg.epk.Publishable tr := by grind
    have sig : msg.sig.Publishable tr := by grind
    have opened : exchange.toOpening.signed.Publishable tr :=
      Opening.signed_publishable (by grind) (vk_publishable (by grind)) epk
    have answered : exchange.signed.Publishable tr :=
      Exchange.signed_publishable opened (dhPk_publishable (by grind))
    have valid : (Concat.concat exchange.signed (DiffieHellman.dh msg.epk drawn)).Invariant tr :=
      agreed_invariant answered epk (by grind)
    have own : drawn.label tr = listenerSecrecy me exchange.listenerKey := by assumption
    have authentic :
        (tr.erase.EventLogged (Event.dialStart dialer exchange.toOpening) ∧
          (exchangeSecrecy dialer me exchange).canFlow
            ((Concat.concat exchange.signed (DiffieHellman.dh msg.epk drawn)).label tr)
            tr.erase) ∨
        (LongTermKeys.label "SAKE PKI" dialer dialerKey).isCorrupt tr.erase := by
      have hashed := hash_publishable opened
      rcases Signature.verify.Invariant dialerKey (Hash.hash exchange.toOpening.signed) msg.sig
        (identityUsage dialer) tr (by grind) (by grind) (by grind) (by grind) verified
        with signed | leaked
      · have signed := signed rfl
        simp only [Signature.SignPred.pred] at signed
        rcases signed with ⟨dialer', opening', secret', usage, same, theirs, label, logged⟩ |
          ⟨listener', exchange', secret', usage, same, -⟩
        · obtain rfl := identityUsage_inj usage
          obtain rfl := Opening.signed_inj (Hash.hash_inj _ _ same)
          have peer : msg.epk = DiffieHellman.dhPk secret' := theirs
          have secrecy := agreed_secrecy (signed := exchange.signed) (theirs := secret')
            (ours := drawn) (tr := tr)
          rw [label, own, ← peer] at secrecy
          exact Or.inl ⟨logged, secrecy⟩
        · exact absurd (Hash.hash_inj _ _ same) (Opening.signed_ne _ _)
      · right
        grind [canFlowPubEqIsCorrupt]
    have known := agreed_known (signed := exchange.signed) (key := msg.epk) (ours := drawn)
      answered
    rw [own] at known
    step
    step by
      simp only [PersistentLocalState.LocalStateInv.invariant]
      exact ⟨by grind, ⟨_, rfl⟩, ⟨key, rfl, by assumption⟩, by grind⟩
    step by
      simp only [PersistentLocalState.LocalStateInv.invariant]
      have ephemeral := dhPk_publishable (tr := tr) (secret := drawn) (by grind)
      grind
    step by
      have hashed : (Hash.hash exchange.signed).Publishable tr := hash_publishable (by grind)
      have pred : Signature.SignPred.pred (identityUsage me) (Signature.vk key)
          (Hash.hash exchange.signed) tr := by
        simp only [Signature.SignPred.pred]
        exact Or.inr ⟨me, exchange, drawn, rfl, rfl, rfl, by assumption, by assumption⟩
      have signature : (Signature.sign key nonce (Hash.hash exchange.signed)).Publishable tr := by
        have := Signature.sign.Invariant key nonce _ (identityUsage me) tr
          ⟨by grind, by grind, by grind, by grind, by grind, Or.inl ⟨rfl, pred⟩⟩
        grind [Signature.sign.label]
      have ephemeral := dhPk_publishable (tr := tr) (secret := drawn) (by grind)
      have confirmed := listener_confirmation_publishable
        (transcript := Concat.concat exchange.signed (DiffieHellman.dh msg.epk drawn))
        (tr := tr) (by grind)
      grind
    step
    grind
  · simp only []
    step
  · simp only []
    step

@[instance]
theorem finishDial.proof (me : Participant) (stHandle msgHandle : Nat) (answered : Std.U64) :
    HoareTriple (finishDial me stHandle msgHandle answered)
      (fun _ => True) (fun _ _ => True) := by
  unfold finishDial
  step
  step
  step
  rw [dial_end_eq, run_ok]
  simp only [pure_bind]
  split_ifs with inside verified confirmed
  · simp only []
    obtain ⟨own, secrecy, ephemeral, transcript, sent, registered, started⟩ :
        kept.secret.Invariant tr ∧
        kept.secret.label tr = dialerSecrecy me kept.opening.dialerKey ∧
        kept.opening.dialerKey = DiffieHellman.dhPk kept.secret ∧
        kept.transcript = kept.opening.signed ∧
        kept.transcript.Publishable tr ∧
        LongTermKeys.IsLongTermPublicKey "SAKE PKI" kept.listener kept.opening.listener tr ∧
        tr.erase.EventLogged (Event.dialStart me kept.opening) := by
      have := ‹PersistentLocalState.LocalStateInv.invariant me kept tr›
      simpa only [PersistentLocalState.LocalStateInv.invariant] using this
    set exchange : Exchange :=
      { kept.opening with answered := answered, listenerKey := msg.epk } with exchange_eq
    have signed :
        Concat.concat (Concat.concat kept.transcript (stamp answered)) msg.epk =
          exchange.signed := by
      rw [transcript]
      rfl
    rw [signed] at verified ⊢
    have epk : msg.epk.Publishable tr := by grind
    have sig : msg.sig.Publishable tr := by grind
    have answer : exchange.signed.Publishable tr :=
      Exchange.signed_publishable (by rw [← transcript]; exact sent) epk
    have valid : (Concat.concat exchange.signed
        (DiffieHellman.dh msg.epk kept.secret)).Invariant tr :=
      agreed_invariant answer epk own
    have authentic :
        (tr.erase.EventLogged (Event.listenStart kept.listener exchange
            (Concat.concat exchange.signed (DiffieHellman.dh msg.epk kept.secret))) ∧
          (exchangeSecrecy me kept.listener exchange).canFlow
            ((Concat.concat exchange.signed (DiffieHellman.dh msg.epk kept.secret)).label tr)
            tr.erase) ∨
        (LongTermKeys.label "SAKE PKI" kept.listener kept.opening.listener).isCorrupt
          tr.erase := by
      have hashed := hash_publishable answer
      rcases Signature.verify.Invariant kept.opening.listener (Hash.hash exchange.signed) msg.sig
        (identityUsage kept.listener) tr (by grind) (by grind) (by grind) (by grind) verified
        with signature | leaked
      · have signature := signature rfl
        simp only [Signature.SignPred.pred] at signature
        rcases signature with ⟨dialer', opening', secret', usage, same, -⟩ |
          ⟨listener', exchange', secret', usage, same, key, label, logged⟩
        · exact absurd (Hash.hash_inj _ _ same).symm (Opening.signed_ne _ _)
        · obtain rfl := identityUsage_inj usage
          obtain rfl : exchange' = exchange := (Exchange.signed_inj (Hash.hash_inj _ _ same)).symm
          have peer : msg.epk = DiffieHellman.dhPk secret' := key
          have shared : DiffieHellman.dh exchange.dialerKey secret' =
              DiffieHellman.dh msg.epk kept.secret := by
            rw [peer, show exchange.dialerKey = DiffieHellman.dhPk kept.secret from ephemeral]
            exact DiffieHellman.dh_commutes _ _
          rw [shared] at logged
          have sealed := agreed_secrecy (signed := exchange.signed) (theirs := secret')
            (ours := kept.secret) (tr := tr)
          rw [label, secrecy, ← peer] at sealed
          exact Or.inl ⟨logged, join_comm_canFlow sealed⟩
      · right
        grind [canFlowPubEqIsCorrupt]
    apply firstTime_then h
    intro unfinished
    mark_non_monotone unfinished
    step by
      simp only [ProtocolEvent.EventInv.invariant]
      exact ⟨unfinished, started, registered,
        authentic.imp (fun ⟨logged, sealed⟩ => ⟨logged, valid, sealed⟩) id⟩
    step by
      exact dialer_confirmation_publishable (by grind) (by assumption)
    grind
  · simp only []
    step
  · simp only []
    step
  · simp only []
    step

/-- A dialer that finished an exchange started its opening. -/
theorem finisher_started {dialer listener : Participant} {exchange : Exchange} {secret : Bytes}
    {tr : ProofTrace} (inv : tr.Invariant)
    (finished : tr.erase.EventLogged (Event.dialFinish dialer listener exchange secret)) :
    tr.erase.EventLogged (Event.dialStart dialer exchange.toOpening) := by
  obtain ⟨time, held⟩ := Trace.EventLogged_imp_EventInv _ tr inv finished
  simp only [ProtocolEvent.EventInv.invariant] at held
  have := held.2.1
  grind

/-- Whoever started an opening holds the signing key of its dialer identity. -/
theorem starter_key {dialer : Participant} {opening : Opening} {tr : ProofTrace}
    (inv : tr.Invariant) (started : tr.erase.EventLogged (Event.dialStart dialer opening)) :
    ∃ key, opening.dialer = Signature.vk key ∧
      LongTermKeys.IsLongTermSecretKey "SAKE PKI" dialer key tr := by
  obtain ⟨time, held⟩ := Trace.EventLogged_imp_EventInv _ tr inv started
  simp only [ProtocolEvent.EventInv.invariant] at held
  obtain ⟨key, identity, owned⟩ := held
  exact ⟨key, identity, LongTermKeys.IsLongTermSecretKey_later "SAKE PKI" dialer key _ tr
    (Trace.prefix_le_self tr time) owned⟩

/-- Two participants that started the same opening are the same: the opening names one
identity key, and a key has one owner. -/
theorem starter_unique {first second : Participant} {opening : Opening} {tr : ProofTrace}
    (inv : tr.Invariant)
    (one : tr.erase.EventLogged (Event.dialStart first opening))
    (other : tr.erase.EventLogged (Event.dialStart second opening)) :
    first = second := by
  obtain ⟨key, identity, owned⟩ := starter_key inv one
  obtain ⟨key', identity', owned'⟩ := starter_key inv other
  obtain rfl := vk_inj (identity.symm.trans identity')
  simp only [LongTermKeys.IsLongTermSecretKey] at owned owned'
  exact owner_unique (owned.2.1.symm.trans owned'.2.1)

/-- The name under which a dialer that finished looked up the listener's identity key is the
name of the participant that holds the key. -/
theorem finisher_expected {dialer expected owner : Participant} {exchange : Exchange}
    {secret key : Bytes} {tr : ProofTrace} (inv : tr.Invariant)
    (finished : tr.erase.EventLogged (Event.dialFinish dialer expected exchange secret))
    (identity : exchange.listener = Signature.vk key)
    (owned : LongTermKeys.IsLongTermSecretKey "SAKE PKI" owner key tr) :
    expected = owner := by
  obtain ⟨time, held⟩ := Trace.EventLogged_imp_EventInv _ tr inv finished
  simp only [ProtocolEvent.EventInv.invariant] at held
  have registered := LongTermKeys.ProofConfig.IsLongTermPublicKey_le
    expected exchange.listener _ tr (Trace.prefix_le_self tr time) held.2.2.1
  simp only [LongTermKeys.IsLongTermSecretKey] at owned
  simp only [LongTermKeys.ProofConfig.IsLongTermPublicKey, identity,
    Bytes.signkeyLabel_vk] at registered
  exact owner_unique (registered.2.1.symm.trans owned.2.1)

@[instance]
theorem finishListen.proof (me : Participant) (stHandle msgHandle : Nat) :
    HoareTriple (finishListen me stHandle msgHandle)
      (fun _ => True) (fun _ _ => True) := by
  unfold finishListen
  step
  step
  rw [listen_end_eq, run_ok]
  simp only [pure_bind]
  split_ifs with confirmed
  · simp only []
    obtain ⟨valid, ⟨shared, transcript⟩, ⟨key, identity, owned⟩, authentic⟩ :
        kept.transcript.Invariant tr ∧
        (∃ shared, kept.transcript = Concat.concat kept.exchange.signed shared) ∧
        (∃ key, kept.exchange.listener = Signature.vk key ∧
          LongTermKeys.IsLongTermSecretKey "SAKE PKI" me key tr) ∧
        ((tr.erase.EventLogged (Event.dialStart kept.dialer kept.exchange.toOpening) ∧
            (exchangeSecrecy kept.dialer me kept.exchange).canFlow (kept.transcript.label tr)
              tr.erase) ∨
          (LongTermKeys.label "SAKE PKI" kept.dialer kept.exchange.dialer).isCorrupt
            tr.erase) := by
      have := ‹PersistentLocalState.LocalStateInv.invariant me kept tr›
      simpa only [PersistentLocalState.LocalStateInv.invariant] using this
    have checked := Mac.mac_checked (code := confirmation) (key := Hash.hash kept.transcript)
      (msg := Literal.literalToBytes (toByteArray dialerLabel)) (tr := tr) (by grind) confirmed
    mark_non_monotone checked
    apply firstTime_then h
    intro unfinished
    mark_non_monotone unfinished
    step by
      simp only [ProtocolEvent.EventInv.invariant]
      refine ⟨unfinished, ?_⟩
      rcases authentic with ⟨started, sealed⟩ | leaked
      · rcases checked with claim | known
        · simp only [Mac.MacPred.pred] at claim
          rcases claim with same | ⟨dialer', listener', exchange', shared', key, -, finished⟩
          · exact absurd same label_ne
          · have agreed := Hash.hash_inj _ _ key
            rw [transcript] at agreed
            obtain ⟨signed, rfl⟩ := concat_inj agreed
            obtain rfl : exchange' = kept.exchange := (Exchange.signed_inj signed).symm
            rw [← transcript] at finished
            obtain rfl := starter_unique h started (finisher_started h finished)
            obtain rfl := finisher_expected h finished identity owned
            exact Or.inl ⟨started, valid, sealed, Or.inl finished⟩
        · refine Or.inl ⟨started, valid, sealed, Or.inr ?_⟩
          grind [Label.canFlow, canFlowPubEqIsCorrupt, Hash.hash.label]
      · exact Or.inr leaked
    grind
  · simp only []
    step

@[instance]
theorem compromiseDialer.proof (handle : Nat) :
    HoareTriple (compromiseDialer handle) (fun _ => True) (fun _ _ => True) := by
  unfold compromiseDialer
  step
  grind

@[instance]
theorem compromiseListener.proof (handle : Nat) :
    HoareTriple (compromiseListener handle) (fun _ => True) (fun _ _ => True) := by
  unfold compromiseListener
  step
  grind

instance : ReachableImpliesInvariant dial.reachability :=
  .mk fun (me, listener, skHandle, pkHandle, ns, now, window) =>
    dial.proof me listener skHandle pkHandle ns now window

instance : ReachableImpliesInvariant listen.reachability :=
  .mk fun (me, dialer, skHandle, pkHandle, msgHandle, ns, now, window, dialed) =>
    listen.proof me dialer skHandle pkHandle msgHandle ns now window dialed

instance : ReachableImpliesInvariant finishDial.reachability :=
  .mk fun (me, stHandle, msgHandle, answered) => finishDial.proof me stHandle msgHandle answered

instance : ReachableImpliesInvariant finishListen.reachability :=
  .mk fun (me, stHandle, msgHandle) => finishListen.proof me stHandle msgHandle

instance : ReachableImpliesInvariant compromiseDialer.reachability :=
  .mk fun handle => compromiseDialer.proof handle

instance : ReachableImpliesInvariant compromiseListener.reachability :=
  .mk fun handle => compromiseListener.proof handle

#combine into ReachabilityTheorem from
  Network,
  Random,
  LongTermKeys "SAKE PKI",
  dial,
  listen,
  finishDial,
  finishListen,
  compromiseDialer,
  compromiseListener,

/-- One time holds one event. -/
theorem same_event {one other : Event} {time : Nat} {tr : ExecTrace}
    (first : tr.EventLoggedAt one time) (second : tr.EventLoggedAt other time) : one = other := by
  rw [Trace.EventLoggedAt_eq_getEventAt] at first second
  exact Option.some.inj (first.symm.trans second)

/-- An event that was logged before a time is logged in the trace up to that time. -/
theorem logged_before {event : Event} {first second : Nat} {tr : ProofTrace}
    (logged : tr.erase.EventLoggedAt event first) (earlier : first < second) :
    (tr.prefix second).erase.EventLogged event := by
  rw [Trace.prefix_erase]
  refine ⟨first, Trace.EventLoggedAt_le' event first _ tr.erase ?_
    (Trace.prefix_le_self _ _) logged⟩
  have := Trace.EventLoggedAt_implies_i_le_length event first tr.erase logged
  grind [Trace.prefix_length]

/-- A dialer finishes an exchange at most once. -/
theorem dial_finish_once {dialer listener : Participant} {exchange : Exchange} {secret : Bytes}
    {first second : Nat} {tr : ProofTrace} (inv : tr.Invariant)
    (one : tr.erase.EventLoggedAt (Event.dialFinish dialer listener exchange secret) first)
    (other : tr.erase.EventLoggedAt (Event.dialFinish dialer listener exchange secret) second) :
    first = second := by
  rcases Nat.lt_trichotomy first second with earlier | same | later
  · have held := Trace.EventLoggedAt_imp_EventInv _ _ _ inv other
    simp only [ProtocolEvent.EventInv.invariant] at held
    exact absurd (logged_before one earlier) held.1
  · exact same
  · have held := Trace.EventLoggedAt_imp_EventInv _ _ _ inv one
    simp only [ProtocolEvent.EventInv.invariant] at held
    exact absurd (logged_before other later) held.1

/-- A listener finishes an exchange at most once. -/
theorem listen_finish_once {listener dialer : Participant} {exchange : Exchange} {secret : Bytes}
    {first second : Nat} {tr : ProofTrace} (inv : tr.Invariant)
    (one : tr.erase.EventLoggedAt (Event.listenFinish listener dialer exchange secret) first)
    (other : tr.erase.EventLoggedAt (Event.listenFinish listener dialer exchange secret) second) :
    first = second := by
  rcases Nat.lt_trichotomy first second with earlier | same | later
  · have held := Trace.EventLoggedAt_imp_EventInv _ _ _ inv other
    simp only [ProtocolEvent.EventInv.invariant] at held
    exact absurd (logged_before one earlier) held.1
  · exact same
  · have held := Trace.EventLoggedAt_imp_EventInv _ _ _ inv one
    simp only [ProtocolEvent.EventInv.invariant] at held
    exact absurd (logged_before other later) held.1

/-- A term that the attacker knows, and that only the holders of a label may know, has been
revealed to the attacker by what makes that label corrupt. -/
theorem revealed_of_known {holders : Label} {secret : Bytes} {time : Nat} {tr : ProofTrace}
    (inv : tr.Invariant) (known : secret.AttackerKnows tr.erase)
    (valid : secret.Invariant (tr.prefix time))
    (sealed : holders.canFlow (secret.label (tr.prefix time)) (tr.prefix time).erase) :
    holders.isCorrupt tr.erase := by
  have published := Bytes.AttackerKnows_implies_Publishable secret tr inv known
  have same := Bytes.label_later_fast secret (tr.prefix time) tr
    (Trace.prefix_le_self tr time) valid
  have later := Trace.erase_le (tr.prefix time) tr (Trace.prefix_le_self tr time)
  rw [same] at sealed
  simp only [Bytes.Publishable] at published
  exact sealed tr.erase later ((canFlowPubEqIsCorrupt _ _).mpr published.2)

end
end Sake
