module
public import Qmdb.Protocol
import all DY.Trace.Manipulation
import all DY.Actions.Network
import all DY.Actions.ProtocolEvent

/-! The client does log what it accepts. `client_authentication` says that every logged event is
authentic; DyLean's Hoare triples are partial, so it would also hold if the client never logged
anything. An attempt sends a message that the attacker knows and runs the registered client on it.
Every attempt is a reachable execution, and when the extracted step accepts the message, the
attempt's trace holds the accepted event. Checked by Lean. -/

namespace Qmdb.Completeness
open DY Aeneas Aeneas.Std Commonware.Symbolic Protocol commonware_symbolic
@[expose] public section

noncomputable section

/-- An attacker-known message carrying `item`, followed by the registered client action. -/
def attempt [Snapshot] (item : Slice Std.U8) (loc : Std.U64) (ws : Slice Bytes) :
    Traceful Unit := do
  let handle ← Network.sendMessage (carrying item)
  client handle loc ws

/-- Every attempt is a reachable protocol execution. -/
theorem attempt_reachable [Snapshot] (item : Slice Std.U8) (loc : Std.U64) (ws : Slice Bytes) :
    ((attempt item loc ws).run Trace.empty).snd.val.Reachable reachability := by
  apply Traceful.PreservesReachability_to_Reachable (pre := fun _ => True)
    (post := fun _ _ => True)
  · intro tr reachable _
    unfold attempt
    apply Traceful.PreservesReachabilityFrom_bind
    · apply Traceful.PreservesReachability_base Network.reachability
    · exact reachable
    · simp [carrying, Literal.attacker_knows_literalToBytes]
    intro handle tr _ reachable _
    apply Traceful.PreservesReachability_base client.reachability _ (handle, loc, ws)
    · exact reachable
    · trivial
  · trivial

theorem run_mk_apply {α : Type} [ExecTraceTypes]
    (f : (tr : ExecTrace) → Option α × { out : ExecTrace // tr ≤ out }) (tr : ExecTrace) :
    (Traceful.mk f).run tr = f tr := by
  rw [Traceful.run_mk]

/-- When the extracted step accepts the message, the trace of the attempt holds the event. -/
theorem attempt_logs [Snapshot] (item : Slice Std.U8) (loc : Std.U64) (ws : Slice Bytes)
    (event : Acceptance)
    (accepted : commonware_symbolic.inclusion.accept_inclusion dyTerms messages () Snapshot.root
      Snapshot.height (carrying item) loc ws = RustM.ok (some event)) :
    ∃ time, ((attempt item loc ws).run Trace.empty).snd.val.EventLoggedAt event time := by
  simp only [attempt, client, receive, accept, Traceful.run_bind, Network.sendMessage,
    Network.receiveMessage, appendEntry, getEntry, ProtocolEvent.logEvent, run_mk_apply,
    Traceful.run_pure, Trace.at?_append]
  have matched : (commonware_symbolic.inclusion.accept_inclusion dyTerms messages () Snapshot.root
      Snapshot.height (carrying item) loc ws).match = MatchResult.ok (some event) := by
    rw [accepted]
    rfl
  rw [matched]
  simp only [Traceful.run_bind, run_mk_apply, Traceful.run_pure, Trace.at?_append]
  exact ⟨_, Trace.at?_append _ _⟩

end

end
end Qmdb.Completeness
