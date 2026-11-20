module
public import Commonware.Symbolic.RustM
public import DY.Actions.Network
public import DY.Actions.ProtocolEvent
import DY.Meta

/-! An extracted client step as a DyLean action. `receive` reads the message at a network handle,
runs the step on it and logs the event that the step accepts; if the step rejects the message or
fails, the action fails and adds nothing to the trace. Each target fixes its trace with `#combine`
and its security policy with a `ProtocolEvent.EventInv` instance.

Trusted: `receive`. Checked: `receive_preserves`, which reduces preservation of the trace
invariant to the event invariant of every event that the step accepts. -/

namespace Commonware.Symbolic
open DY Aeneas Aeneas.Std
@[expose] public section

variable [BytesFunctor] [ExecTraceTypes] [ExecTraceTypes.Has Network.ExecEntryT]
variable {Event : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Event)]

/-- Receive the message at `handle` and log the event that `step` accepts for it, or fail. -/
def receive (step : Bytes → RustM (Option Event)) (handle : Nat) : Traceful Unit := do
  let message ← Network.receiveMessage handle
  match (step message).match with
  | .ok (some event) => ProtocolEvent.logEvent event
  | _ => failure

variable [ProofTraceTypes] [TraceInvariant] [BytesInvariants] [BytesInvariantsProofs]
  [ProofTraceTypes.Has Network.ProofEntryT] [TraceInvariant.Has Network.ProofEntryT]
  [ProtocolEvent.EventInv Event] [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT Event)]
  [TraceInvariant.Has (ProtocolEvent.ProofEntryT Event)]

/-- `receive` preserves the trace invariant if every event that `step` accepts, for any message,
satisfies the event invariant on every trace. -/
theorem receive_preserves (step : Bytes → RustM (Option Event)) (handle : Nat)
    (sound : ∀ message event, step message = RustM.ok (some event) →
      ∀ tr, ProtocolEvent.EventInv.invariant tr event) :
    HoareTriple (receive step handle) (fun _ => True) (fun _ _ => True) := by
  unfold receive
  step
  split
  · rename_i event accepted
    step by exact sound _ _ (eq_ok_of_match accepted) _
    trivial
  · step

end
end Commonware.Symbolic
