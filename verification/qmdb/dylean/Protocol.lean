module
public import Correspondence
public import DY.Actions.Network
public import DY.Actions.ProtocolEvent
import DY.Meta

/-! The DyLean protocol around the extracted client decision. Trusted: `client`, the event
invariant and the theorem statements. `referenceClient` is an executable copy of the client with
the reference decision; `client_eq_reference` proves the two equal, so the sanity checks can run
it. -/

namespace Qmdb.Protocol
open DY Aeneas Aeneas.Std
@[expose] public section

abbrev Acceptance := Reference.Acceptance

#combine +toplevel into ExecEntryT, baseAttackerKnowledge from
  Network,
  ProtocolEvent Acceptance,

/-- The client with the reference decision. Untrusted and executable. -/
def referenceClient [Snapshot] (handle : Nat) (loc : Std.U64) (ws : Slice Bytes) :
    Traceful Unit := do
  let message ← Network.receiveMessage handle
  match Reference.step message loc ws with
  | some event => ProtocolEvent.logEvent event
  | none => failure

noncomputable section

/-- Receive a claimed item and log the event that the extracted Rust decision returns. -/
def client [Snapshot] (handle : Nat) (loc : Std.U64) (ws : Slice Bytes) : Traceful Unit := do
  let message ← Network.receiveMessage handle
  match (qmdb_dylean.client.client_step dyTerms Snapshot.root Snapshot.height message loc ws).match
  with
  | .ok (some event) => ProtocolEvent.logEvent event
  | _ => failure

theorem client_eq_reference [Snapshot] :
    (client : Nat → Std.U64 → Slice Bytes → Traceful Unit) = referenceClient := by
  funext handle loc ws
  unfold client referenceClient
  congr 1
  funext message
  rw [Correspondence.client_step_eq, RustM.match.ok]
  cases Reference.step message loc ws <;> rfl

def client.reachability [Snapshot] : ReachabilityConfig :=
  .make fun (handle, loc, ws) => client handle loc ws

section
variable [Snapshot]
#combine into ReachabilityConfig from
  Network,
  client,
end

#combine +toplevel into ProofEntryT from
  Network,
  ProtocolEvent Acceptance,

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Literal,
  Concat,
  Hash,

instance [Snapshot] : ProtocolEvent.EventInv Acceptance where
  invariant _ event := event.height = Snapshot.height ∧
    event.location.val < 2^event.height.val ∧ event.item = Snapshot.items event.location.val

section
variable [Snapshot]
#combine +toplevel into SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  Network,
  ProtocolEvent Acceptance,

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Literal,
  Concat,
  Hash,

theorem referenceClient_preserves (handle : Nat) (loc : Std.U64) (ws : Slice Bytes) :
    HoareTriple (referenceClient handle loc ws) (fun _ => True) (fun _ _ => True) := by
  unfold referenceClient
  step
  split
  · rename_i event accepted
    step by
      simp only [ProtocolEvent.EventInv.invariant]
      exact Correspondence.step_sound _ _ _ _ accepted
    trivial
  · step

theorem client_preserves (handle : Nat) (loc : Std.U64) (ws : Slice Bytes) :
    HoareTriple (client handle loc ws) (fun _ => True) (fun _ _ => True) := by
  rw [client_eq_reference]
  exact referenceClient_preserves handle loc ws

instance : ReachableImpliesInvariant client.reachability :=
  .mk (fun (handle, loc, ws) => client_preserves handle loc ws)

#combine into ReachabilityTheorem from
  Network,
  client,

/-- Every acceptance on a reachable trace names the snapshot height, an in-range location and
the item stored there. -/
theorem client_authentication (event : Acceptance) (time : Nat) :
    ∀ tr : ExecTrace, tr.Reachable reachability → tr.EventLoggedAt event time →
      event.height = Snapshot.height ∧ event.location.val < 2^event.height.val ∧
        event.item = Snapshot.items event.location.val := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv logged
  exact Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged
end

#print axioms client_eq_reference
#print axioms client_authentication

end
end
end Qmdb.Protocol
