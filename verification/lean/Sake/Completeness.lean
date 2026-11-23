module
public import Sake.Steps
public import Sake.Protocol
import all DY.Trace.Basic
import all DY.Trace.Manipulation
import all DY.Actions.Network
import all DY.Actions.Random
import all DY.Actions.ProtocolEvent
import all DY.Actions.PersistentGlobalState
import all DY.Actions.PersistentLocalState
import all DY.Actions.LongTermKeys
import DY.Meta

/-! The handshake can finish. Checked.

The trace statements of `Sake.SecurityTheorems` hold on every reachable trace, and DyLean's
Hoare triples are partial, so they would also hold if an action could never finish.
`both_finish` schedules the actions of `Sake.Protocol` for one handshake: both peers register an
identity key, the dialer starts, the listener answers, the dialer finishes and the listener
finishes. When each peer's timestamp is inside the other's window, every action succeeds, and
the trace they leave is reachable and holds both finishes of one exchange with one secret
transcript.

The run is evaluated action by action. `Runs` says that an action succeeds on a trace with a
result and a trace after it. Each action of the protocol has a lemma that says what it must
find on the trace, where it leaves what the next action reads and which event it logs. A finish
is logged only once, so the lemmas also track which events a trace holds.

This uses the bodies of DyLean's actions (`import all`), because DyLean exports them only
through their Hoare triples. Only `both_finish` is public: the lemmas before it name the random
value that DyLean draws at a position of the trace, which DyLean does not export. -/

namespace Sake.Completeness
open DY DY.Comparse Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic

noncomputable section

/-! ## Runs -/

/-- `action` succeeds on `tr` with `result` and leaves the trace `out`. -/
def Runs {α : Type} (action : Traceful α) (tr : ExecTrace) (result : α) (out : ExecTrace) :
    Prop :=
  ∃ later : tr ≤ out, action.run tr = (some result, ⟨out, later⟩)

theorem Runs.pure {α : Type} (result : α) (tr : ExecTrace) :
    Runs (pure result) tr result tr :=
  ⟨Trace.le_refl tr, Traceful.run_pure result tr⟩

theorem Runs.bind {α β : Type} {first : Traceful α} {rest : α → Traceful β}
    {tr mid out : ExecTrace} {a : α} {b : β}
    (ran : Runs first tr a mid) (then_ran : Runs (rest a) mid b out) :
    Runs (first >>= rest) tr b out := by
  obtain ⟨early, ran⟩ := ran
  obtain ⟨late, then_ran⟩ := then_ran
  refine ⟨Trace.le_trans _ _ _ early late, ?_⟩
  rw [Traceful.run_bind, ran]
  simp only [then_ran]

theorem guard_runs {holds : Prop} [Decidable holds] (met : holds) (tr : ExecTrace) :
    Runs (guard holds) tr () tr := by
  simp only [guard, met, ↓reduceIte]
  exact Runs.pure _ _

theorem run_runs {α : Type} {step : RustM α} {result : α} (returned : step = RustM.ok result)
    (tr : ExecTrace) : Runs (run step) tr result tr := by
  rw [returned, run_ok]
  exact Runs.pure _ _

theorem parse_runs {α : Type} [ParseableSerializeable α] (value : α) (tr : ExecTrace) :
    Runs (liftM (parse (serialize value) : Err α)) tr value tr := by
  refine ⟨Trace.le_refl tr, ?_⟩
  simp only [liftM, monadLift, MonadLift.monadLift, parse_serialize_inv]
  rw [Traceful.run_mk]

/-! ## Entries -/

theorem appendEntry_runs {E : Type} [ExecTraceTypes.Has E] (entry : E) (tr : ExecTrace) :
    Runs (appendEntry entry) tr tr.length (tr.append entry) := by
  refine ⟨Trace.append_le tr entry, ?_⟩
  rw [appendEntry, Traceful.run_mk]

theorem getEntry_runs {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {handle : Nat}
    {entry : E} (held : tr.at? handle = some entry) : Runs (getEntry handle) tr entry tr := by
  refine ⟨Trace.le_refl tr, ?_⟩
  rw [getEntry, Traceful.run_mk]
  simp only [held]

/-- An entry stays where it is when the trace grows by one entry. -/
theorem at?_append_of_some {E F : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has F]
    {tr : ExecTrace} {handle : Nat} {found : F} (entry : E)
    (held : tr.at? handle = some found) : (tr.append entry).at? handle = some found := by
  have grown := Trace.at?_le (EntryT := F) tr (tr.append entry) handle (Trace.append_le tr entry)
  simp only [held] at grown
  exact grown

/-- The entry that keeps `state` for `who`. -/
abbrev keeping {S : Type} (who : Participant) (state : S) :
    PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S) :=
  { st := { participant := who, state } }

/-- The entry that registers `key` as the identity key of `who`. -/
abbrev registering (who : Participant) (key : Bytes) :
    PersistentGlobalState.State.ExecEntryT (LongTermKeys.PublicKeyState "SAKE PKI") :=
  { st := { p := who, pk := key } }

theorem send_runs (msg : Bytes) (tr : ExecTrace) :
    Runs (Network.sendMessage msg) tr tr.length (tr.append (Network.ExecEntryT.mk msg)) :=
  appendEntry_runs _ _

theorem receive_runs {tr : ExecTrace} {handle : Nat} {msg : Bytes}
    (held : tr.at? handle = some (Network.ExecEntryT.mk msg)) :
    Runs (Network.receiveMessage handle) tr msg tr :=
  Runs.bind (getEntry_runs held) (Runs.pure _ _)

theorem genRand_runs (size : Nat) (tr : ExecTrace) :
    Runs (Random.genRand size) tr (Random.makeRand tr.length size)
      (tr.append ({ length := size } : Random.ExecEntryT)) :=
  Runs.bind (appendEntry_runs _ _) (Runs.pure _ _)

theorem logEvent_runs (event : Event) (tr : ExecTrace) :
    Runs (ProtocolEvent.logEvent event) tr () (tr.append (ProtocolEvent.ExecEntryT.mk event)) :=
  Runs.bind (appendEntry_runs _ _) (Runs.pure _ _)

theorem storeLocal_runs {S : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
    (who : Participant) (state : S) (tr : ExecTrace) :
    Runs (PersistentLocalState.storeLocalState who state) tr tr.length
      (tr.append (keeping who state)) :=
  appendEntry_runs _ _

theorem getLocal_runs {S : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
    {tr : ExecTrace} {handle : Nat} {who : Participant} {state : S}
    (held : tr.at? handle = some (keeping who state)) :
    Runs (PersistentLocalState.getLocalState who handle) tr state tr :=
  Runs.bind (Runs.bind (getEntry_runs held) (Runs.pure _ _))
    (Runs.bind (guard_runs rfl _) (Runs.pure _ _))

theorem getPrivateKey_runs {tr : ExecTrace} {handle : Nat} {who : Participant} {key : Bytes}
    (held : tr.at? handle =
      some (keeping who ({ sk := key } : LongTermKeys.SecretKeyState "SAKE PKI"))) :
    Runs (LongTermKeys.getPrivateKey "SAKE PKI" who handle) tr key tr :=
  Runs.bind (getLocal_runs held) (Runs.pure _ _)

theorem getPublicKey_runs {tr : ExecTrace} {handle : Nat} {who : Participant} {key : Bytes}
    (held : tr.at? handle = some (registering who key)) :
    Runs (LongTermKeys.getPublicKey "SAKE PKI" who handle) tr key tr :=
  Runs.bind (Runs.bind (getEntry_runs held) (Runs.pure _ _))
    (Runs.bind (guard_runs rfl _) (Runs.pure _ _))

/-! ## Logged events -/

theorem inj_injective {E : Type} [ExecTraceTypes.Has E] {a b : E}
    (same : (TraceEntryHas.inj a : ExecTrace.Entry) = TraceEntryHas.inj b) : a = b := by
  have first : TraceEntryHas.proj (TraceEntryHas.inj a : ExecTrace.Entry) = some a := by
    rw [TraceEntryHas.inj_proj_eq]
  have second : TraceEntryHas.proj (TraceEntryHas.inj b : ExecTrace.Entry) = some b := by
    rw [TraceEntryHas.inj_proj_eq]
  rw [same, second] at first
  exact (Option.some.inj first).symm

/-- A lookup in a trace that grew by one entry. -/
theorem at?_append {E F : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has F]
    (tr : ExecTrace) (entry : E) (handle : Nat) :
    ((tr.append entry).at? handle : Option F) =
      if handle < tr.length then tr.at? handle
      else if handle = tr.length then
        TraceEntryHas.proj (TraceEntryHas.inj entry : ExecTrace.Entry)
      else none := by
  simp only [Trace.at?, Trace.at, Trace.append, Trace.length, Array.size_push,
    Array.getElem_push]
  grind

/-- The events of a trace that grew by one entry are those it had, and the entry if it is an
event. -/
theorem eventLogged_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (entry : E)
    (event : Event) :
    (tr.append entry).EventLogged event ↔
      tr.EventLogged event ∨
        (TraceEntryHas.inj entry : ExecTrace.Entry) =
          TraceEntryHas.inj (ProtocolEvent.ExecEntryT.mk event) := by
  simp only [Trace.EventLogged, Trace.EventLoggedAt, at?_append]
  constructor
  · rintro ⟨handle, found⟩
    split_ifs at found with inside last
    · exact Or.inl ⟨handle, found⟩
    · right
      rwa [TraceEntryHas.inj_proj_eq] at found
  · rintro (⟨handle, found⟩ | same)
    · refine ⟨handle, ?_⟩
      have inside : handle < tr.length := by
        have := Trace.at?_eq_some_implies_length_le
          (EntryT := ProtocolEvent.ExecEntryT Event) tr handle
        simpa only [found] using this
      simpa only [inside, ↓reduceIte] using found
    · refine ⟨tr.length, ?_⟩
      simp only [Nat.lt_irrefl, ↓reduceIte]
      rw [TraceEntryHas.inj_proj_eq, same]

theorem eventLogged_empty (event : Event) : ¬ (Trace.empty : ExecTrace).EventLogged event := by
  rintro ⟨handle, found⟩
  simp [Trace.EventLoggedAt, Trace.at?, Trace.empty, Trace.length] at found

/-- Logging an event adds that event. -/
theorem eventLogged_event (tr : ExecTrace) (logged event : Event) :
    (tr.append (ProtocolEvent.ExecEntryT.mk logged)).EventLogged event ↔
      tr.EventLogged event ∨ event = logged := by
  rw [eventLogged_append]
  constructor
  · rintro (before | same)
    · exact Or.inl before
    · cases inj_injective same
      exact Or.inr rfl
  · rintro (before | rfl)
    · exact Or.inl before
    · exact Or.inr rfl

/-- Closes the goal that an entry of another kind than an event adds no event: the kinds of
entry have different tags in the trace. -/
macro "other_entry" : tactic =>
  `(tactic| (
    rw [eventLogged_append]
    refine or_iff_left fun same => ?_
    have tags := congrArg (fun entry : ExecTrace.Entry => entry.id) same
    exact absurd tags (of_decide_eq_false rfl)))

theorem eventLogged_message (tr : ExecTrace) (msg : Bytes) (event : Event) :
    (tr.append (Network.ExecEntryT.mk msg)).EventLogged event ↔ tr.EventLogged event := by
  other_entry

theorem eventLogged_random (tr : ExecTrace) (size : Nat) (event : Event) :
    (tr.append ({ length := size } : Random.ExecEntryT)).EventLogged event ↔
      tr.EventLogged event := by
  other_entry

theorem eventLogged_dialing (tr : ExecTrace) (who : Participant) (state : Dialing)
    (event : Event) :
    (tr.append (keeping who state)).EventLogged event ↔ tr.EventLogged event := by
  other_entry

theorem eventLogged_listening (tr : ExecTrace) (who : Participant) (state : Listening)
    (event : Event) :
    (tr.append (keeping who state)).EventLogged event ↔ tr.EventLogged event := by
  other_entry

theorem eventLogged_dialerSecret (tr : ExecTrace) (who : Participant) (state : DialerSecret)
    (event : Event) :
    (tr.append (keeping who state)).EventLogged event ↔ tr.EventLogged event := by
  other_entry

theorem eventLogged_listenerSecret (tr : ExecTrace) (who : Participant)
    (state : ListenerSecret) (event : Event) :
    (tr.append (keeping who state)).EventLogged event ↔ tr.EventLogged event := by
  other_entry

theorem eventLogged_secretKey (tr : ExecTrace) (who : Participant)
    (state : LongTermKeys.SecretKeyState "SAKE PKI") (event : Event) :
    (tr.append (keeping who state)).EventLogged event ↔ tr.EventLogged event := by
  other_entry

theorem eventLogged_publicKey (tr : ExecTrace) (who : Participant) (key : Bytes)
    (event : Event) :
    (tr.append (registering who key)).EventLogged event ↔ tr.EventLogged event := by
  other_entry

/-! ## Reachability -/

/-- A step of the protocol that runs on a reachable trace leaves a reachable trace. -/
theorem Runs.reachable (sub : ReachabilityConfig) [ReachabilityConfig.Has sub reachability]
    (input : sub.Input) {tr out : ExecTrace} {result : (sub.step input).fst}
    (allowed : sub.PreCond input tr) (ran : Runs (sub.step input).snd tr result out)
    (reached : tr.Reachable reachability) : out.Reachable reachability := by
  obtain ⟨later, ran⟩ := ran
  have step := Traceful.PreservesReachability_base sub reachability input tr reached allowed
  simp only [Traceful.PreservesReachabilityFrom, ran] at step
  exact step.1

/-- What an action finds on a trace, it finds on the trace it leaves. -/
theorem Runs.at? {α F : Type} [ExecTraceTypes.Has F] {action : Traceful α}
    {tr out : ExecTrace} {result : α} (ran : Runs action tr result out) {handle : Nat}
    {found : F} (held : tr.at? handle = some found) : out.at? handle = some found := by
  have grown := Trace.at?_le (EntryT := F) tr out handle ran.1
  simp only [held] at grown
  exact grown

/-! ## The actions -/

/-- The opening of a dialer with the identity key `key` and the ephemeral secret `x`. -/
def opened (ns : ByteArray) (key listener : Bytes) (dialed : Std.U64) (x : Bytes) : Opening :=
  { ns, dialer := Signature.vk key, listener, dialed, dialerKey := DiffieHellman.dhPk x }

/-- The exchange in which a listener with the ephemeral secret `y` answers `opening`. -/
def answer (opening : Opening) (answered : Std.U64) (y : Bytes) : Exchange :=
  { opening with answered, listenerKey := DiffieHellman.dhPk y }

/-- The secret transcript of that exchange. -/
def agreed (opening : Opening) (answered : Std.U64) (y : Bytes) : Bytes :=
  Concat.concat (answer opening answered y).signed (DiffieHellman.dh opening.dialerKey y)

/-- The `Syn` of a dialer. -/
def synOf (opening : Opening) (key nonce : Bytes) : SynMessage :=
  { epk := opening.dialerKey, sig := Signature.sign key nonce (Hash.hash opening.signed) }

/-- The `SynAck` of a listener. -/
def synAckOf (opening : Opening) (answered : Std.U64) (y key nonce : Bytes) : SynAckMessage :=
  { epk := DiffieHellman.dhPk y,
    sig := Signature.sign key nonce (Hash.hash (answer opening answered y).signed),
    confirmation := confirmation (agreed opening answered y) listenerLabel }

/-- Registering gives `who` an identity key at the returned handles and logs no event. -/
theorem register_runs (who : Participant) (tr : ExecTrace) :
    ∃ (msgHandle pkHandle skHandle : Nat) (out : ExecTrace) (key : Bytes),
      Runs (LongTermKeys.generateKeyPair "SAKE PKI" who) tr (msgHandle, pkHandle, skHandle)
        out ∧
      out.at? pkHandle = some (registering who (Signature.vk key)) ∧
      out.at? skHandle =
        some (keeping who ({ sk := key } : LongTermKeys.SecretKeyState "SAKE PKI")) ∧
      ∀ event : Event, out.EventLogged event ↔ tr.EventLogged event := by
  refine ⟨?msgHandle, ?pkHandle, ?skHandle, ?out, Random.makeRand tr.length 32, ?runs,
    ?registered, ?kept, ?events⟩
  case runs =>
    refine Runs.bind (genRand_runs 32 tr) ?_
    refine Runs.bind (send_runs _ _) ?_
    refine Runs.bind (appendEntry_runs _ _) ?_
    refine Runs.bind (storeLocal_runs _ _ _) ?_
    exact Runs.pure _ _
  case registered => exact at?_append_of_some _ (Trace.at?_append _ _)
  case kept => exact Trace.at?_append _ _
  case events =>
    intro event
    simp only [eventLogged_secretKey, eventLogged_publicKey, eventLogged_message,
      eventLogged_random]

/-- A dialer that finds its identity key and the listener's starts: it keeps its opening, sends
its `Syn` and logs that it started. -/
theorem dial_runs (me listener : Participant) (skHandle pkHandle : Nat) (ns : ByteArray)
    (now : Std.U64) (window : sake.Window) (tr : ExecTrace) (key listenerKey : Bytes)
    (own : tr.at? skHandle =
      some (keeping me ({ sk := key } : LongTermKeys.SecretKeyState "SAKE PKI")))
    (theirs : tr.at? pkHandle = some (registering listener listenerKey)) :
    ∃ (stHandle secretHandle msgHandle : Nat) (out : ExecTrace) (x nonce : Bytes),
      Runs (dial me listener skHandle pkHandle ns now window) tr
        (stHandle, secretHandle, msgHandle) out ∧
      out.at? stHandle = some (keeping me ({
        listener, opening := opened ns key listenerKey now x, secret := x,
        transcript := (opened ns key listenerKey now x).signed, window } : Dialing)) ∧
      out.at? msgHandle = some (Network.ExecEntryT.mk
        (serialize (synOf (opened ns key listenerKey now x) key nonce))) ∧
      ∀ event : Event, out.EventLogged event ↔
        tr.EventLogged event ∨ event = Event.dialStart me (opened ns key listenerKey now x) := by
  refine ⟨?stHandle, ?secretHandle, ?msgHandle, ?out, Random.makeRand tr.length 32,
    Random.makeRand (tr.append ({ length := 32 } : Random.ExecEntryT)).length 32,
    ?runs, ?kept, ?sent, ?events⟩
  case runs =>
    unfold dial
    refine Runs.bind (getPrivateKey_runs own) ?_
    refine Runs.bind (getPublicKey_runs theirs) ?_
    refine Runs.bind (genRand_runs 32 _) ?_
    refine Runs.bind (genRand_runs 32 _) ?_
    refine Runs.bind (run_runs (dial_start_eq ..) _) ?_
    refine Runs.bind (logEvent_runs _ _) ?_
    refine Runs.bind (storeLocal_runs _ _ _) ?_
    refine Runs.bind (storeLocal_runs _ _ _) ?_
    refine Runs.bind (send_runs _ _) ?_
    exact Runs.pure _ _
  case kept => exact at?_append_of_some _ (at?_append_of_some _ (Trace.at?_append _ _))
  case sent => exact Trace.at?_append _ _
  case events =>
    intro event
    simp only [eventLogged_message, eventLogged_dialerSecret, eventLogged_dialing,
      eventLogged_event, eventLogged_random]
    rfl

/-- The listener's step accepts the `Syn` of the dialer it looked up. -/
theorem listen_start_accepts (ns : ByteArray) (now dialed : Std.U64) (window : sake.Window)
    (key answerNonce dialerKey x nonce y : Bytes) {opening : Opening}
    (shape : opening = opened ns dialerKey (Signature.vk key) dialed x)
    (inside : window.start ≤ dialed ∧ dialed < window.end) :
    sake.listen_start sakeTerms signer peer fresh ()
      { early := true, transcript := start ns, now, window, signer := ⟨key, answerNonce⟩,
        peer := Signature.vk dialerKey } y
      { time_ms := dialed, epk := (synOf opening dialerKey nonce).epk,
        sig := (synOf opening dialerKey nonce).sig } =
    RustM.ok (.Ok (agreed opening now y,
      { time_ms := now, epk := (synAckOf opening now y key answerNonce).epk,
        sig := (synAckOf opening now y key answerNonce).sig,
        confirmation := (synAckOf opening now y key answerNonce).confirmation })) := by
  subst shape
  rw [listen_start_eq]
  simp only [synOf, synAckOf, opened, answer, agreed, inside, Signature.verify_sign, and_self,
    ↓reduceIte]

/-- The dialer's step accepts the `SynAck` of the listener it dialed. -/
theorem dial_end_accepts (ns : ByteArray) (key listenerKey : Bytes) (dialed answered : Std.U64)
    (window : sake.Window) (x y nonce : Bytes) {opening : Opening}
    (shape : opening = opened ns key (Signature.vk listenerKey) dialed x)
    (inside : window.start ≤ answered ∧ answered < window.end) :
    sake.dial_end sakeTerms peer () x opening.signed opening.listener window
      { time_ms := answered, epk := (synAckOf opening answered y listenerKey nonce).epk,
        sig := (synAckOf opening answered y listenerKey nonce).sig,
        confirmation := (synAckOf opening answered y listenerKey nonce).confirmation } =
    RustM.ok (.Ok (confirmation (agreed opening answered y) dialerLabel,
      agreed opening answered y)) := by
  subst shape
  rw [dial_end_eq]
  simp only [synAckOf, opened, answer, agreed, Exchange.signed, inside, Signature.verify_sign,
    DiffieHellman.dh_commutes y x, and_self, ↓reduceIte]

/-- The listener's last step accepts the confirmation of its own transcript. -/
theorem listen_end_accepts (secret : Bytes) :
    sake.listen_end sakeTerms () secret (confirmation secret dialerLabel) =
      RustM.ok (.Some secret) := by
  rw [listen_end_eq]
  simp only [↓reduceIte]

theorem firstTime_runs {event : Event} {tr : ExecTrace} (unlogged : ¬ tr.EventLogged event) :
    Runs (firstTime event) tr () tr := by
  refine ⟨Trace.le_refl tr, ?_⟩
  simp only [firstTime]
  rw [Traceful.run_mk]
  simp only [unlogged, ↓reduceIte]

/-- A listener that finds its identity key, the dialer's and the dialer's `Syn` answers: it
keeps the exchange with its secret transcript, sends its `SynAck` and logs that it answered. -/
theorem listen_runs (me dialer : Participant) (skHandle pkHandle msgHandle : Nat)
    (ns : ByteArray) (now : Std.U64) (window : sake.Window) (dialed : Std.U64)
    (tr : ExecTrace) (key dialerKey x nonce : Bytes) {opening : Opening}
    (shape : opening = opened ns dialerKey (Signature.vk key) dialed x)
    (inside : window.start ≤ dialed ∧ dialed < window.end)
    (own : tr.at? skHandle =
      some (keeping me ({ sk := key } : LongTermKeys.SecretKeyState "SAKE PKI")))
    (theirs : tr.at? pkHandle = some (registering dialer (Signature.vk dialerKey)))
    (syn : tr.at? msgHandle =
      some (Network.ExecEntryT.mk (serialize (synOf opening dialerKey nonce)))) :
    ∃ (stHandle secretHandle answerHandle : Nat) (out : ExecTrace) (y answerNonce : Bytes),
      Runs (listen me dialer skHandle pkHandle msgHandle ns now window dialed) tr
        (stHandle, secretHandle, answerHandle) out ∧
      out.at? stHandle = some (keeping me ({
        dialer, exchange := answer opening now y, transcript := agreed opening now y }
          : Listening)) ∧
      out.at? answerHandle = some (Network.ExecEntryT.mk
        (serialize (synAckOf opening now y key answerNonce))) ∧
      ∀ event : Event, out.EventLogged event ↔
        tr.EventLogged event ∨
          event = Event.listenStart me (answer opening now y) (agreed opening now y) := by
  subst shape
  refine ⟨?stHandle, ?secretHandle, ?answerHandle, ?out, Random.makeRand tr.length 32,
    Random.makeRand (tr.append ({ length := 32 } : Random.ExecEntryT)).length 32,
    ?runs, ?kept, ?sent, ?events⟩
  case runs =>
    unfold listen
    refine Runs.bind (receive_runs syn) ?_
    refine Runs.bind (parse_runs _ _) ?_
    refine Runs.bind (getPrivateKey_runs own) ?_
    refine Runs.bind (getPublicKey_runs theirs) ?_
    refine Runs.bind (genRand_runs 32 _) ?_
    refine Runs.bind (genRand_runs 32 _) ?_
    refine Runs.bind (run_runs (listen_start_accepts ns now dialed window key _ dialerKey x
      nonce _ rfl inside) _) ?_
    refine Runs.bind (logEvent_runs _ _) ?_
    refine Runs.bind (storeLocal_runs _ _ _) ?_
    refine Runs.bind (storeLocal_runs _ _ _) ?_
    refine Runs.bind (send_runs _ _) ?_
    exact Runs.pure _ _
  case kept => exact at?_append_of_some _ (at?_append_of_some _ (Trace.at?_append _ _))
  case sent => exact Trace.at?_append _ _
  case events =>
    intro event
    simp only [eventLogged_message, eventLogged_listenerSecret, eventLogged_listening,
      eventLogged_event, eventLogged_random]
    rfl

/-- A dialer that finds what it kept and the `SynAck` of the listener it dialed finishes, if it
has not finished this exchange before: it sends its confirmation and logs that it finished. -/
theorem finishDial_runs (me listener : Participant) (stHandle msgHandle : Nat)
    (answered : Std.U64) (tr : ExecTrace) (ns : ByteArray) (key listenerKey : Bytes)
    (dialed : Std.U64) (window : sake.Window) (x y nonce : Bytes) {opening : Opening}
    (shape : opening = opened ns key (Signature.vk listenerKey) dialed x)
    (inside : window.start ≤ answered ∧ answered < window.end)
    (kept : tr.at? stHandle = some (keeping me ({
      listener, opening, secret := x, transcript := opening.signed, window } : Dialing)))
    (synAck : tr.at? msgHandle = some (Network.ExecEntryT.mk
      (serialize (synAckOf opening answered y listenerKey nonce))))
    (unfinished : ¬ tr.EventLogged
      (Event.dialFinish me listener (answer opening answered y) (agreed opening answered y))) :
    ∃ (ackHandle : Nat) (out : ExecTrace),
      Runs (finishDial me stHandle msgHandle answered) tr ackHandle out ∧
      out.at? ackHandle = some (Network.ExecEntryT.mk
        (confirmation (agreed opening answered y) dialerLabel)) ∧
      ∀ event : Event, out.EventLogged event ↔
        tr.EventLogged event ∨ event =
          Event.dialFinish me listener (answer opening answered y)
            (agreed opening answered y) := by
  refine ⟨?ackHandle, ?out, ?runs, ?sent, ?events⟩
  case runs =>
    unfold finishDial
    refine Runs.bind (getLocal_runs kept) ?_
    refine Runs.bind (receive_runs synAck) ?_
    refine Runs.bind (parse_runs _ _) ?_
    refine Runs.bind (run_runs (dial_end_accepts ns key listenerKey dialed answered window x y
      nonce shape inside) _) ?_
    refine Runs.bind (firstTime_runs unfinished) ?_
    refine Runs.bind (logEvent_runs _ _) ?_
    exact send_runs _ _
  case sent => exact Trace.at?_append _ _
  case events =>
    intro event
    simp only [eventLogged_message, eventLogged_event]
    rfl

/-- A listener that finds what it kept and the dialer's confirmation of its transcript
finishes, if it has not finished this exchange before: it logs that it finished. -/
theorem finishListen_runs (me dialer : Participant) (stHandle msgHandle : Nat) (tr : ExecTrace)
    (exchange : Exchange) (secret : Bytes)
    (kept : tr.at? stHandle =
      some (keeping me ({ dialer, exchange, transcript := secret } : Listening)))
    (ack : tr.at? msgHandle =
      some (Network.ExecEntryT.mk (confirmation secret dialerLabel)))
    (unfinished : ¬ tr.EventLogged (Event.listenFinish me dialer exchange secret)) :
    ∃ out : ExecTrace,
      Runs (finishListen me stHandle msgHandle) tr () out ∧
      ∀ event : Event, out.EventLogged event ↔
        tr.EventLogged event ∨ event = Event.listenFinish me dialer exchange secret := by
  refine ⟨?out, ?runs, ?events⟩
  case runs =>
    unfold finishListen
    refine Runs.bind (getLocal_runs kept) ?_
    refine Runs.bind (receive_runs ack) ?_
    refine Runs.bind (run_runs (listen_end_accepts secret) _) ?_
    refine Runs.bind (firstTime_runs unfinished) ?_
    exact logEvent_runs _ _
  case events =>
    intro event
    simp only [eventLogged_event]

/-! ## A handshake -/

/-- The attacker can schedule the actions of the protocol so that both peers finish one
exchange with one secret transcript: when each peer's timestamp is inside the other's window,
a reachable trace holds both finishes. -/
public theorem both_finish (dialer listener : Participant) (ns : ByteArray)
    (dialed answered : Std.U64) (dialerWindow listenerWindow : sake.Window)
    (early : listenerWindow.start ≤ dialed ∧ dialed < listenerWindow.end)
    (late : dialerWindow.start ≤ answered ∧ answered < dialerWindow.end) :
    ∃ (tr : ExecTrace) (exchange : Exchange) (secret : Bytes),
      tr.Reachable reachability ∧
      exchange.ns = ns ∧
      exchange.dialed = dialed ∧
      exchange.answered = answered ∧
      tr.EventLogged (Event.dialFinish dialer listener exchange secret) ∧
      tr.EventLogged (Event.listenFinish listener dialer exchange secret) := by
  obtain ⟨_, dialerPk, dialerSk, tr₁, dialerKey, ran₁, dialerPub, dialerSec, events₁⟩ :=
    register_runs dialer Trace.empty
  obtain ⟨_, listenerPk, listenerSk, tr₂, listenerKey, ran₂, listenerPub, listenerSec,
    events₂⟩ := register_runs listener tr₁
  obtain ⟨dialing, _, syn, tr₃, x, nonce, ran₃, kept, sent, events₃⟩ :=
    dial_runs dialer listener dialerSk listenerPk ns dialed dialerWindow tr₂ dialerKey
      (Signature.vk listenerKey) (ran₂.at? dialerSec) listenerPub
  obtain ⟨listening, _, synAck, tr₄, y, answerNonce, ran₄, answering, answer_sent, events₄⟩ :=
    listen_runs listener dialer listenerSk dialerPk syn ns answered listenerWindow dialed tr₃
      listenerKey dialerKey x nonce rfl early (ran₃.at? listenerSec)
      (ran₃.at? (ran₂.at? dialerPub)) sent
  have dialer_unfinished : ¬ tr₄.EventLogged (Event.dialFinish dialer listener
      (answer (opened ns dialerKey (Signature.vk listenerKey) dialed x) answered y)
      (agreed (opened ns dialerKey (Signature.vk listenerKey) dialed x) answered y)) := by
    simp [events₄, events₃, events₂, events₁, eventLogged_empty]
  obtain ⟨ack, tr₅, ran₅, confirmed, events₅⟩ :=
    finishDial_runs dialer listener dialing synAck answered tr₄ ns dialerKey listenerKey dialed
      dialerWindow x y answerNonce rfl late (ran₄.at? kept) answer_sent dialer_unfinished
  have listener_unfinished : ¬ tr₅.EventLogged (Event.listenFinish listener dialer
      (answer (opened ns dialerKey (Signature.vk listenerKey) dialed x) answered y)
      (agreed (opened ns dialerKey (Signature.vk listenerKey) dialed x) answered y)) := by
    simp [events₅, events₄, events₃, events₂, events₁, eventLogged_empty]
  obtain ⟨tr₆, ran₆, events₆⟩ :=
    finishListen_runs listener dialer listening ack tr₅ _ _ (ran₅.at? answering) confirmed
      listener_unfinished
  refine ⟨tr₆, _, _, ?_, rfl, rfl, rfl, (events₆ _).mpr (Or.inl ((events₅ _).mpr (Or.inr rfl))),
    (events₆ _).mpr (Or.inr rfl)⟩
  have reached₁ := ran₁.reachable (LongTermKeys.generateKeyPair.reachability "SAKE PKI") dialer
    trivial Trace.Reachable.Base
  have reached₂ := ran₂.reachable (LongTermKeys.generateKeyPair.reachability "SAKE PKI")
    listener trivial reached₁
  have reached₃ := ran₃.reachable dial.reachability
    (dialer, listener, dialerSk, listenerPk, ns, dialed, dialerWindow) trivial reached₂
  have reached₄ := ran₄.reachable listen.reachability
    (listener, dialer, listenerSk, dialerPk, syn, ns, answered, listenerWindow, dialed) trivial
    reached₃
  have reached₅ := ran₅.reachable finishDial.reachability (dialer, dialing, synAck, answered)
    trivial reached₄
  exact ran₆.reachable finishListen.reachability (listener, listening, ack) trivial reached₅

end

end Sake.Completeness
