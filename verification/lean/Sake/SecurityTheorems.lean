module
public import Sake.Proof
import DY.Meta

/-! What the SAKE target proves. Trusted: the four statements.

`handshake_completes` and `foreign_signature_rejected` speak about the extracted steps alone.
The two authentication statements hold on every trace that the attacker can reach with the
actions of `Sake.Protocol`: it controls the network and the schedule, and it can compromise any
identity key.

The statements say nothing about freshness. A listener that finishes has checked the dialer's
confirmation, but DyLean has no theory in which that check authenticates the dialer, so
`listener_authentication` rests on the dialer's signature alone and a replayed `Syn` satisfies
it. They also say nothing about the secrecy of the transcript. -/

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
identity key was compromised before. -/
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
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged
  simp only [ProtocolEvent.EventInv.invariant] at this
  simpa [LongTermKeys.label] using this

/-- Authentication of the dialer. On every reachable trace, a listener that
finishes a handshake with a dialer finishes an exchange whose opening this
dialer started earlier, unless the dialer's identity key was compromised
before. The opening names the namespace, both identity keys, the dialer's
timestamp and its ephemeral key. Nothing here says that the opening is
fresh: a recorded `Syn` that is replayed inside the listener's window
satisfies this statement. -/
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
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged
  simp only [ProtocolEvent.EventInv.invariant] at this
  simpa [LongTermKeys.label] using this

end
end Sake
