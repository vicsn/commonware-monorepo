module
public import Sake.Protocol
public import Sake.Steps
import DY.Meta

/-! The invariant that every reachable trace of the SAKE protocol satisfies. Checked.

An identity key signs only two kinds of transcript: the one a dialer signs once it has logged
that it started, and the one a listener signs once it has logged that it answered. The two are
told apart by `Opening.signed_ne`. A dialer that verifies the listener's signature therefore
finds the listener's answer on the trace, unless the listener's identity key is compromised, and
a listener that verifies the dialer's signature finds the dialer's start. The event invariant
records these two facts for the events that finish a handshake, and each action is shown to
preserve the invariant over the extracted step it runs. -/

namespace Sake
open DY DY.Comparse Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-! ## Messages -/

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

/-! ## What terms and entries must satisfy -/

#combine +toplevel into ProofEntryT from
  Network,
  Random,
  ProtocolEvent Event,
  PersistentLocalState.State Dialing,
  PersistentLocalState.State Listening,
  LongTermKeys "SAKE PKI",

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
of a listener that logged its answer with the secret transcript that its ephemeral key gives. -/
instance signPred : Signature.SignPred where
  pred usage _ msg tr :=
    (∃ dialer opening,
      usage = identityUsage dialer ∧
      msg = Hash.hash opening.signed ∧
      tr.erase.EventLogged (Event.dialStart dialer opening)) ∨
    (∃ listener exchange secret,
      usage = identityUsage listener ∧
      msg = Hash.hash exchange.signed ∧
      exchange.listenerKey = DiffieHellman.dhPk secret ∧
      tr.erase.EventLogged (Event.listenStart listener exchange
        (Concat.concat exchange.signed (DiffieHellman.dh exchange.dialerKey secret))))

instance [BytesInvariants] : Signature.SignPredProof where
  pred_later := by
    intro _ _ _ _ _ _ _ _ _ _ _ signed
    rcases signed with ⟨dialer, opening, h⟩ | ⟨listener, exchange, secret, h⟩
    · exact Or.inl ⟨dialer, opening, by grind⟩
    · exact Or.inr ⟨listener, exchange, secret, by grind⟩

/-- Every derived value is public: the handshake derives only the confirmations that it
sends. -/
instance : KdfExpand.KdfExpandInvariant where
  usage _ _ := Usage.nothing
  label _ _ _ := Label.pub

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,
  KdfExpand,

@[grind]
instance : LongTermKeys.ProofConfig "SAKE PKI" identityUsage (LongTermKeys.label "SAKE PKI") where
  IsLongTermPublicKey who vk tr :=
    vk.Publishable tr ∧
    vk.signkeyLabel tr = LongTermKeys.label "SAKE PKI" who vk ∧
    vk.SignkeyHasUsage (identityUsage who) tr
  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

/-- What a dialer keeps is the secret of its ephemeral key and the transcript of its opening,
for a listener whose identity key it looked up. -/
instance dialingInv : PersistentLocalState.LocalStateInv Dialing where
  invariant _ kept tr :=
    kept.secret.Invariant tr ∧
    kept.opening.dialerKey = DiffieHellman.dhPk kept.secret ∧
    kept.transcript = kept.opening.signed ∧
    kept.transcript.Publishable tr ∧
    LongTermKeys.IsLongTermPublicKey "SAKE PKI" kept.listener kept.opening.listener tr
  invariant_later := by grind

/-- A listener keeps a transcript only for an opening that the dialer it looked up started,
unless that dialer's identity key is compromised. -/
instance listeningInv : PersistentLocalState.LocalStateInv Listening where
  invariant _ kept tr :=
    tr.erase.EventLogged (Event.dialStart kept.dialer kept.exchange.toOpening) ∨
    (LongTermKeys.label "SAKE PKI" kept.dialer kept.exchange.dialer).isCorrupt tr.erase
  invariant_later := by grind

/-- A dialer finishes only an exchange that the listener it looked up answered with the same
secret transcript, and a listener finishes only an exchange whose opening the dialer it looked
up started, unless the identity key of that peer is compromised. -/
instance eventInv : ProtocolEvent.EventInv Event where
  invariant tr event :=
    match event with
    | .dialStart _ _ => True
    | .listenStart _ _ _ => True
    | .dialFinish _ listener exchange secret =>
      tr.erase.EventLogged (Event.listenStart listener exchange secret) ∨
      (LongTermKeys.label "SAKE PKI" listener exchange.listener).isCorrupt tr.erase
    | .listenFinish _ dialer exchange _ =>
      tr.erase.EventLogged (Event.dialStart dialer exchange.toOpening) ∨
      (LongTermKeys.label "SAKE PKI" dialer exchange.dialer).isCorrupt tr.erase

#combine +toplevel into SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  Network,
  Random,
  ProtocolEvent Event,
  PersistentLocalState.State Dialing,
  PersistentLocalState.State Listening,
  LongTermKeys "SAKE PKI",

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,
  KdfExpand,

/-! ## Terms that may be sent -/

theorem stamp_publishable (time : Std.U64) (tr : ProofTrace) : (stamp time).Publishable tr := by
  simp only [stamp]
  grind [Literal.literalToBytes.Invariant, Literal.literalToBytes.label]

theorem start_publishable (ns : ByteArray) (tr : ProofTrace) : (start ns).Publishable tr := by
  simp only [start]
  grind [Hash.hash.Invariant, Hash.hash.label, Literal.literalToBytes.Invariant,
    Literal.literalToBytes.label]

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

theorem confirmation_publishable {transcript : Bytes} (label : Slice Std.U8) {tr : ProofTrace}
    (valid : transcript.Invariant tr) : (confirmation transcript label).Publishable tr := by
  have used : (Hash.hash transcript).HasUsage ((Hash.hash transcript).usage tr) tr := Or.inl rfl
  have flows : ((confirmation transcript label).label tr).canFlow Label.pub tr.erase :=
    (KdfExpand.kdfExpand.label (Hash.hash transcript)
      (Literal.literalToBytes (toByteArray label)) 32 _ tr used).1
  simp only [confirmation] at flows ⊢
  grind [KdfExpand.kdfExpand.Invariant, Hash.hash.Invariant, Literal.literalToBytes.Invariant]

/-- The secret transcript of an exchange is a valid term when the peer's ephemeral key came
from the network and the local ephemeral secret is valid. -/
theorem agreed_invariant {signed key secret : Bytes} {tr : ProofTrace}
    (transcript : signed.Publishable tr) (peer : key.Publishable tr)
    (own : secret.Invariant tr) :
    (Concat.concat signed (DiffieHellman.dh key secret)).Invariant tr := by
  have shared := DiffieHellman.dh.Invariant key secret tr ⟨by grind, own⟩
  grind [Concat.concat.Invariant]

/-! ## Every action preserves the invariant -/

attribute [local grind] ProtocolEvent.EventInv.invariant
attribute [local grind] eventInv
attribute [local grind] Signature.SignPred.pred
attribute [local grind] signPred
attribute [local grind] PersistentLocalState.LocalStateInv.invariant
attribute [local grind] dialingInv
attribute [local grind] listeningInv
attribute [local grind] LongTermKeys.IsLongTermPublicKey
attribute [local grind] LongTermKeys.IsLongTermSecretKey

@[instance]
theorem dial.proof (me listener : Participant) (skHandle pkHandle : Nat) (ns : ByteArray)
    (now : Std.U64) (window : sake.Window) :
    HoareTriple (dial me listener skHandle pkHandle ns now window)
      (fun _ => True) (fun _ _ => True) := by
  unfold dial
  step
  step
  step with ⟨fun _ => Label.secret, Usage.nothing⟩
  step with ⟨fun _ => Label.secret, Usage.nothing⟩
  rw [dial_start_eq, run_ok]
  simp only [pure_bind]
  step
  set opening : Opening :=
    { ns, dialer := Signature.vk key, listener := listenerKey, dialed := now,
      dialerKey := DiffieHellman.dhPk drawn } with opening_eq
  have signed : opening.signed.Publishable tr :=
    Opening.signed_publishable (vk_publishable (by grind)) (by grind) (dhPk_publishable (by grind))
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step by
    have pred : Signature.SignPred.pred (identityUsage me) (Signature.vk key)
        (Hash.hash opening.signed) tr := by
      simp only [Signature.SignPred.pred]
      exact Or.inl ⟨me, opening, rfl, rfl, by assumption⟩
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
  step with ⟨fun _ => Label.secret, Usage.nothing⟩
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
    have authentic : tr.erase.EventLogged (Event.dialStart dialer exchange.toOpening) ∨
        (LongTermKeys.label "SAKE PKI" dialer dialerKey).isCorrupt tr.erase := by
      have hashed := hash_publishable opened
      rcases Signature.verify.Invariant dialerKey (Hash.hash exchange.toOpening.signed) msg.sig
        (identityUsage dialer) tr (by grind) (by grind) (by grind) (by grind) verified
        with signed | leaked
      · have signed := signed rfl
        simp only [Signature.SignPred.pred] at signed
        rcases signed with ⟨dialer', opening', usage, same, logged⟩ |
          ⟨listener', exchange', secret', usage, same, -⟩
        · obtain rfl := identityUsage_inj usage
          obtain rfl := Opening.signed_inj (Hash.hash_inj _ _ same)
          exact Or.inl logged
        · exact absurd (Hash.hash_inj _ _ same) (Opening.signed_ne _ _)
      · right
        grind [canFlowPubEqIsCorrupt]
    have answered : exchange.signed.Publishable tr :=
      Exchange.signed_publishable opened (dhPk_publishable (by grind))
    step
    step by
      simp only [PersistentLocalState.LocalStateInv.invariant]
      grind
    step by
      have hashed : (Hash.hash exchange.signed).Publishable tr := hash_publishable (by grind)
      have pred : Signature.SignPred.pred (identityUsage me) (Signature.vk key)
          (Hash.hash exchange.signed) tr := by
        simp only [Signature.SignPred.pred]
        exact Or.inr ⟨me, exchange, drawn, rfl, rfl, rfl, by assumption⟩
      have signature : (Signature.sign key nonce (Hash.hash exchange.signed)).Publishable tr := by
        have := Signature.sign.Invariant key nonce _ (identityUsage me) tr
          ⟨by grind, by grind, by grind, by grind, by grind, Or.inl ⟨rfl, pred⟩⟩
        grind [Signature.sign.label]
      have ephemeral := dhPk_publishable (tr := tr) (secret := drawn) (by grind)
      have confirmed := confirmation_publishable listenerLabel
        (agreed_invariant (signed := exchange.signed) (key := msg.epk) (secret := drawn)
          (tr := tr) (by grind) (by grind) (by grind))
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
    obtain ⟨own, ephemeral, transcript, sent, registered⟩ :
        kept.secret.Invariant tr ∧
        kept.opening.dialerKey = DiffieHellman.dhPk kept.secret ∧
        kept.transcript = kept.opening.signed ∧
        kept.transcript.Publishable tr ∧
        LongTermKeys.IsLongTermPublicKey "SAKE PKI" kept.listener kept.opening.listener tr := by
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
    have authentic :
        tr.erase.EventLogged (Event.listenStart kept.listener exchange
          (Concat.concat exchange.signed (DiffieHellman.dh msg.epk kept.secret))) ∨
        (LongTermKeys.label "SAKE PKI" kept.listener kept.opening.listener).isCorrupt
          tr.erase := by
      have hashed := hash_publishable answer
      rcases Signature.verify.Invariant kept.opening.listener (Hash.hash exchange.signed) msg.sig
        (identityUsage kept.listener) tr (by grind) (by grind) (by grind) (by grind) verified
        with signature | leaked
      · have signature := signature rfl
        simp only [Signature.SignPred.pred] at signature
        rcases signature with ⟨dialer', opening', usage, same, -⟩ |
          ⟨listener', exchange', secret', usage, same, key, logged⟩
        · exact absurd (Hash.hash_inj _ _ same).symm (Opening.signed_ne _ _)
        · obtain rfl := identityUsage_inj usage
          obtain rfl : exchange' = exchange := (Exchange.signed_inj (Hash.hash_inj _ _ same)).symm
          have shared : DiffieHellman.dh exchange.dialerKey secret' =
              DiffieHellman.dh msg.epk kept.secret := by
            have peer : msg.epk = DiffieHellman.dhPk secret' := key
            rw [peer, show exchange.dialerKey = DiffieHellman.dhPk kept.secret from ephemeral]
            exact DiffieHellman.dh_commutes _ _
          rw [shared] at logged
          exact Or.inl logged
      · right
        grind [canFlowPubEqIsCorrupt]
    have derived := confirmation_publishable dialerLabel
      (agreed_invariant (secret := kept.secret) answer epk own)
    step by
      simp only [ProtocolEvent.EventInv.invariant]
      exact authentic
    step
    grind
  · simp only []
    step
  · simp only []
    step
  · simp only []
    step

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
    have authentic := ‹PersistentLocalState.LocalStateInv.invariant me kept tr›
    simp only [PersistentLocalState.LocalStateInv.invariant] at authentic
    step by
      simp only [ProtocolEvent.EventInv.invariant]
      exact authentic
    grind
  · simp only []
    step

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

#combine into ReachabilityTheorem from
  Network,
  Random,
  LongTermKeys "SAKE PKI",
  dial,
  listen,
  finishDial,
  finishListen,

end
end Sake
