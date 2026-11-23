module
public import Commonware.Symbolic.RustM
public import DY.Actions.Network
public import DY.Actions.ProtocolEvent
import DY.Meta

/-! An extracted client step as a DyLean action. `accept` logs the event that a step accepts; if
the step rejects or fails, the action fails and adds nothing to the trace. `receive` reads the
message at a network handle and accepts the step on it. `run` returns what a step returns, for a
target whose action goes on to store state or send a message. Each target fixes its trace with
`#combine` and its security policy with a `ProtocolEvent.EventInv` instance.

Trusted: `accept`, `receive` and `run`. Checked: `accept_preserves` and `receive_preserves`,
which reduce preservation of the trace invariant to the event invariant of every event that the
step accepts, and `run_ok` and `run_returns`, which let a proof about an action use that the
step returned its result. -/

namespace Commonware.Symbolic
open DY Aeneas Aeneas.Std
@[expose] public section

section
variable [ExecTraceTypes] {α : Type}

/-- Run `step` and return its result. If the step does not return, the action
fails and adds nothing to the trace. -/
def run (step : RustM α) : Traceful α :=
  match step.match with
  | .ok result => pure result
  | _ => failure

theorem run_ok (result : α) : run (RustM.ok result) = pure result := by
  simp [run]

variable [ProofTraceTypes] [TraceInvariant]

/-- An action continues after `run step` only with a result that `step` returned. -/
@[instance]
theorem run_returns (step : RustM α) :
    HoareTriple (run step) (fun _ => True) (fun result _ => step = RustM.ok result) := by
  apply HoareTriple.mk
  unfold run hoareTriple
  intro tr _ inv
  split
  · rename_i result returned
    have returns := eq_ok_of_match returned
    step
    simp_all
  · step

end

section
variable [ExecTraceTypes] {Event : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Event)]

/-- Log the event that `step` accepts, or fail. -/
def accept (step : RustM (Option Event)) : Traceful Unit :=
  match step.match with
  | .ok (some event) => ProtocolEvent.logEvent event
  | _ => failure

variable [ProofTraceTypes] [TraceInvariant] [ProtocolEvent.EventInv Event]
  [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT Event)]
  [TraceInvariant.Has (ProtocolEvent.ProofEntryT Event)]

/-- `accept` preserves the trace invariant from a precondition if every event that `step`
accepts satisfies the event invariant on every trace where the precondition holds. -/
theorem accept_preserves (step : RustM (Option Event)) (pre : ProofTrace → Prop)
    (sound : ∀ event, step = RustM.ok (some event) →
      ∀ tr, pre tr → ProtocolEvent.EventInv.invariant tr event) :
    HoareTriple (accept step) pre (fun _ _ => True) := by
  apply HoareTriple.mk
  unfold accept hoareTriple
  intro tr holds inv
  mark_non_monotone holds
  split
  · rename_i event accepted
    step by exact sound _ (eq_ok_of_match accepted) _ holds
    trivial
  · step

end

variable [BytesFunctor] [ExecTraceTypes] [ExecTraceTypes.Has Network.ExecEntryT]
variable {Event : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Event)]

/-- Receive the message at `handle` and log the event that `step` accepts for
it, or fail. -/
def receive
    (step : Bytes → RustM (Option Event)) (handle : Nat) :
    Traceful Unit := do
  let message ← Network.receiveMessage handle
  accept (step message)

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
  unfold receive accept
  step
  split
  · rename_i event accepted
    step by exact sound _ _ (eq_ok_of_match accepted) _
    trivial
  · step

end
end Commonware.Symbolic
