module
public import Sake.Proof
import Sake.Completeness
import DY.Meta

/-! What the SAKE target proves. Trusted: the ten statements.

`handshake_completes` and `foreign_signature_rejected` speak about the extracted steps alone.
`handshake_reachable` says that the attacker can reach a trace on which both peers finish, so
the statements about every reachable trace are not empty. The other seven hold on every trace
that the attacker can reach with the actions of `Sake.Protocol`: it controls the network and the
schedule, and it can compromise any identity key and what any peer keeps between its steps.

- `dialer_authentication`: for the dialer, the listener answered this exchange with this
  transcript.
- `listener_authentication`: for the listener, the dialer started this opening.
- `listener_key_confirmation`: for the listener, the dialer finished this exchange with this
  listener and this transcript.
- `dialer_injective_agreement` and `listener_injective_agreement`: no event of a peer matches
  two finishes.
- `dialer_secrecy` and `listener_secrecy`: the attacker does not know the transcript.

Authentication, key confirmation and secrecy each hold unless the identity key of the peer was
compromised before the handshake finished. Key confirmation and secrecy also fail when what
either peer keeps for the exchange is compromised: the dialer's ephemeral secret or the
listener's secret transcript. Secrecy does not fail when an identity key is compromised after
the handshake finished. The agreement statements hold without a condition. Nothing here speaks
about time, about V0 or about the record protocol. -/

namespace Sake
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-- Honest runs complete. When each peer's timestamp is inside the other's
window, the four extracted steps accept each other's messages, and both
peers end with the same secret transcript. -/
theorem handshake_completes
    (ns : ByteArray) (dialed answered : Std.U64)
    (dialerWindow listenerWindow : sake.Window)
    (dialer listener : Signer) (x y : Bytes)
    (early : listenerWindow.start ≤ dialed ∧ dialed < listenerWindow.end)
    (late : dialerWindow.start ≤ answered ∧ answered < dialerWindow.end) :
    ∃ kept syn secret synAck confirmation,
      sake.dial_start sakeTerms signer peer fresh ()
        { early := true, transcript := start ns, now := dialed,
          window := dialerWindow, signer := dialer,
          peer := Signature.vk listener.key } x =
        RustM.ok (x, kept, syn) ∧
      sake.listen_start sakeTerms signer peer fresh ()
        { early := true, transcript := start ns, now := answered,
          window := listenerWindow, signer := listener,
          peer := Signature.vk dialer.key } y syn =
        RustM.ok (.Ok (secret, synAck)) ∧
      sake.dial_end sakeTerms peer () x kept (Signature.vk listener.key)
          dialerWindow synAck =
        RustM.ok (.Ok (confirmation, secret)) ∧
      sake.listen_end sakeTerms () secret confirmation =
        RustM.ok (.Some secret) := by
  obtain ⟨dialerKey, dialerNonce⟩ := dialer
  obtain ⟨listenerKey, listenerNonce⟩ := listener
  simp only [dial_start_eq, listen_start_eq, dial_end_eq, listen_end_eq]
  refine ⟨_, _, ?secret, ?synAck, ?confirmation, rfl, ?_, ?_, ?_⟩
  rotate_left 3
  · simp only [early, Signature.verify_sign, and_self, ↓reduceIte]
    rfl
  · simp only [late, Exchange.signed, Signature.verify_sign, DiffieHellman.dh_commutes y x,
      and_self, ↓reduceIte]
    rfl
  · simp [Exchange.signed]

/-- Honest runs complete on a trace. When each peer's timestamp is inside
the other's window, the attacker can schedule the actions so that both peers
finish: some reachable trace holds the finish of the dialer and the finish
of the listener, for one exchange with these timestamps in this namespace
and one secret transcript. -/
theorem handshake_reachable
    (dialer listener : Participant) (ns : ByteArray)
    (dialed answered : Std.U64)
    (dialerWindow listenerWindow : sake.Window)
    (early : listenerWindow.start ≤ dialed ∧ dialed < listenerWindow.end)
    (late : dialerWindow.start ≤ answered ∧ answered < dialerWindow.end) :
    ∃ (tr : ExecTrace) (exchange : Exchange) (secret : Bytes),
      tr.Reachable reachability ∧
      exchange.ns = ns ∧
      exchange.dialed = dialed ∧
      exchange.answered = answered ∧
      tr.EventLogged (Event.dialFinish dialer listener exchange secret) ∧
      tr.EventLogged (Event.listenFinish listener dialer exchange secret) :=
  Completeness.both_finish dialer listener ns dialed answered dialerWindow
    listenerWindow early late

/-- A dialer rejects a `SynAck` that carries the listener's signature of
another transcript than the one the dialer holds, for example of an exchange
with another ephemeral key. -/
theorem foreign_signature_rejected
    (secret transcript other : Bytes) (listener : Signer)
    (window : sake.Window) (msg : sake.SynAck Bytes Bytes Bytes)
    (inside : window.start ≤ msg.time_ms ∧ msg.time_ms < window.end)
    (signed : msg.sig =
      Signature.sign listener.key listener.nonce (Hash.hash other))
    (foreign : other ≠
      Concat.concat (Concat.concat transcript (stamp msg.time_ms)) msg.epk) :
    sake.dial_end sakeTerms peer () secret transcript
        (Signature.vk listener.key) window msg =
      RustM.ok (.Err .Signature) := by
  have rejected := verify_other (key := listener.key) (nonce := listener.nonce)
    (fun same => foreign (Hash.hash_inj _ _ same).symm)
  rw [dial_end_eq]
  simp only [inside, signed, rejected, and_self, ↓reduceIte, Bool.false_eq_true]

/-- Authentication of the listener. On every reachable trace, a dialer that
finishes a handshake with a listener finishes an exchange that this listener
answered earlier with the same secret transcript, unless the listener's
identity key was compromised before. The listener therefore holds the
transcript that the dialer returns. -/
theorem dialer_authentication
    (dialer listener : Participant) (exchange : Exchange) (secret : Bytes)
    (time : Nat) :
    ∀ tr : ExecTrace,
      tr.Reachable reachability →
      tr.EventLoggedAt
        (Event.dialFinish dialer listener exchange secret) time →
      (tr.prefix time).EventLogged
        (Event.listenStart listener exchange secret) ∨
      LongTermKeys.LongTermKeyCompromised "SAKE PKI" listener
        exchange.listener (tr.prefix time) := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv logged
  have held := Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged
  simp only [ProtocolEvent.EventInv.invariant] at held
  rcases held.2.2.2 with ⟨answered, -⟩ | leaked
  · left
    simpa using answered
  · right
    simpa [LongTermKeys.label] using leaked

/-- Authentication of the dialer. On every reachable trace, a listener that
finishes a handshake with a dialer finishes an exchange whose opening this
dialer started earlier, unless the dialer's identity key was compromised
before. The opening names the namespace, both identity keys, the dialer's
timestamp and its ephemeral key. Nothing here says that the opening is
fresh: a recorded `Syn` that is replayed inside the listener's window
satisfies this statement. `listener_key_confirmation` says more. -/
theorem listener_authentication
    (listener dialer : Participant) (exchange : Exchange) (secret : Bytes)
    (time : Nat) :
    ∀ tr : ExecTrace,
      tr.Reachable reachability →
      tr.EventLoggedAt
        (Event.listenFinish listener dialer exchange secret) time →
      (tr.prefix time).EventLogged
        (Event.dialStart dialer exchange.toOpening) ∨
      LongTermKeys.LongTermKeyCompromised "SAKE PKI" dialer
        exchange.dialer (tr.prefix time) := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv logged
  have held := Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged
  simp only [ProtocolEvent.EventInv.invariant] at held
  rcases held.2 with ⟨started, -⟩ | leaked
  · left
    simpa using started
  · right
    simpa [LongTermKeys.label] using leaked

/-- Key confirmation for the listener. On every reachable trace, a listener
that finishes a handshake with a dialer finishes an exchange that this
dialer finished earlier with the same secret transcript, unless the dialer's
identity key or what either peer keeps for the exchange was compromised
before. The listener checks the dialer's confirmation, and only a dialer
that finished with this transcript, or an attacker that knows the
transcript, computes it. A replayed `Syn` does not satisfy this statement:
the dialer's finish names the listener's timestamp and ephemeral key. -/
theorem listener_key_confirmation
    (listener dialer : Participant) (exchange : Exchange) (secret : Bytes)
    (time : Nat) :
    ∀ tr : ExecTrace,
      tr.Reachable reachability →
      tr.EventLoggedAt
        (Event.listenFinish listener dialer exchange secret) time →
      (tr.prefix time).EventLogged
        (Event.dialFinish dialer listener exchange secret) ∨
      LongTermKeys.LongTermKeyCompromised "SAKE PKI" dialer
        exchange.dialer (tr.prefix time) ∨
      DialerCompromised dialer exchange.dialerKey (tr.prefix time) ∨
      ListenerCompromised listener exchange.listenerKey (tr.prefix time) := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv logged
  have held := Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged
  simp only [ProtocolEvent.EventInv.invariant] at held
  rcases held.2 with ⟨-, -, -, finished | known⟩ | leaked
  · left
    simpa using finished
  · right
    right
    simpa [exchangeSecrecy, dialerSecrecy, listenerSecrecy] using known
  · right
    left
    simpa [LongTermKeys.label] using leaked

/-- Injective agreement for the dialer. On every reachable trace, two
finishes of dialers that are matched by the same answer of a listener are
the same finish. With `dialer_authentication`, each finish of a dialer has
an answer of its listener that no other finish shares. -/
theorem dialer_injective_agreement
    (dialer₁ listener₁ : Participant) (exchange₁ : Exchange) (secret₁ : Bytes)
    (dialer₂ listener₂ : Participant) (exchange₂ : Exchange) (secret₂ : Bytes)
    (finished₁ finished₂ answered : Nat) :
    ∀ tr : ExecTrace,
      tr.Reachable reachability →
      tr.EventLoggedAt
        (Event.dialFinish dialer₁ listener₁ exchange₁ secret₁) finished₁ →
      tr.EventLoggedAt
        (Event.dialFinish dialer₂ listener₂ exchange₂ secret₂) finished₂ →
      tr.EventLoggedAt
        (Event.listenStart listener₁ exchange₁ secret₁) answered →
      tr.EventLoggedAt
        (Event.listenStart listener₂ exchange₂ secret₂) answered →
      finished₁ = finished₂ := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv one other first second
  obtain ⟨rfl, rfl, rfl⟩ := Event.listenStart.inj (same_event first second)
  obtain rfl := starter_unique inv (finisher_started inv ⟨_, one⟩)
    (finisher_started inv ⟨_, other⟩)
  exact dial_finish_once inv one other

/-- Injective agreement for the listener. On every reachable trace, two
finishes of listeners that are matched by the same finish of a dialer are
the same finish. With `listener_key_confirmation`, each finish of a listener
has a finish of its dialer that no other finish shares. -/
theorem listener_injective_agreement
    (listener₁ dialer₁ : Participant) (exchange₁ : Exchange) (secret₁ : Bytes)
    (listener₂ dialer₂ : Participant) (exchange₂ : Exchange) (secret₂ : Bytes)
    (finished₁ finished₂ matched : Nat) :
    ∀ tr : ExecTrace,
      tr.Reachable reachability →
      tr.EventLoggedAt
        (Event.listenFinish listener₁ dialer₁ exchange₁ secret₁) finished₁ →
      tr.EventLoggedAt
        (Event.listenFinish listener₂ dialer₂ exchange₂ secret₂) finished₂ →
      tr.EventLoggedAt
        (Event.dialFinish dialer₁ listener₁ exchange₁ secret₁) matched →
      tr.EventLoggedAt
        (Event.dialFinish dialer₂ listener₂ exchange₂ secret₂) matched →
      finished₁ = finished₂ := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv one other first second
  obtain ⟨rfl, rfl, rfl, rfl⟩ := Event.dialFinish.inj (same_event first second)
  exact listen_finish_once inv one other

/-- Secrecy for the dialer. On every reachable trace, the attacker knows the
secret transcript of a handshake that a dialer finished with a listener only
if the listener's identity key was compromised before the dialer finished,
or what either peer keeps for the exchange is compromised at some time. A
compromise of an identity key after the dialer finished does not reveal the
transcript. -/
theorem dialer_secrecy
    (dialer listener : Participant) (exchange : Exchange) (secret : Bytes)
    (time : Nat) :
    ∀ tr : ExecTrace,
      tr.Reachable reachability →
      tr.EventLoggedAt
        (Event.dialFinish dialer listener exchange secret) time →
      secret.AttackerKnows tr →
      LongTermKeys.LongTermKeyCompromised "SAKE PKI" listener
        exchange.listener (tr.prefix time) ∨
      DialerCompromised dialer exchange.dialerKey tr ∨
      ListenerCompromised listener exchange.listenerKey tr := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv logged known
  have held := Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged
  simp only [ProtocolEvent.EventInv.invariant] at held
  rcases held.2.2.2 with ⟨-, valid, sealed⟩ | leaked
  · right
    simpa [exchangeSecrecy, dialerSecrecy, listenerSecrecy] using
      revealed_of_known inv known valid sealed
  · left
    simpa [LongTermKeys.label] using leaked

/-- Secrecy for the listener. On every reachable trace, the attacker knows
the secret transcript of a handshake that a listener finished with a dialer
only if the dialer's identity key was compromised before the listener
finished, or what either peer keeps for the exchange is compromised at some
time. A compromise of an identity key after the listener finished does not
reveal the transcript. -/
theorem listener_secrecy
    (listener dialer : Participant) (exchange : Exchange) (secret : Bytes)
    (time : Nat) :
    ∀ tr : ExecTrace,
      tr.Reachable reachability →
      tr.EventLoggedAt
        (Event.listenFinish listener dialer exchange secret) time →
      secret.AttackerKnows tr →
      LongTermKeys.LongTermKeyCompromised "SAKE PKI" dialer
        exchange.dialer (tr.prefix time) ∨
      DialerCompromised dialer exchange.dialerKey tr ∨
      ListenerCompromised listener exchange.listenerKey tr := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv logged known
  have held := Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged
  simp only [ProtocolEvent.EventInv.invariant] at held
  rcases held.2 with ⟨-, valid, sealed, -⟩ | leaked
  · right
    simpa [exchangeSecrecy, dialerSecrecy, listenerSecrecy] using
      revealed_of_known inv known valid sealed
  · left
    simpa [LongTermKeys.label] using leaked

end
end Sake
