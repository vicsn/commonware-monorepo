module
public import Leaf.Step
public import Commonware.Symbolic.Client
import DY.Meta

/-! The DyLean protocol around the extracted leaf client. Trusted: `client`, the event invariant,
the `#combine` configuration and the theorem statement. The client is the shared
`Commonware.Symbolic.receive` action over the extracted `client_step`, so preservation of the
trace invariant reduces to `Step.client_step_sound`. -/

namespace Leaf.Protocol
open DY Aeneas Aeneas.Std Commonware.Symbolic
@[expose] public section

abbrev Acceptance := commonware_symbolic.leaf.Acceptance

#combine +toplevel into ExecEntryT, baseAttackerKnowledge from
  Network,
  ProtocolEvent Acceptance,

noncomputable section

/-- Receive a message and log the event that the extracted Rust decision returns. -/
def client [Commitment] (handle : Nat) : Traceful Unit :=
  receive (fun message => commonware_symbolic.leaf.client_step dyTerms messages ()
    Commitment.digest message) handle

def client.reachability [Commitment] : ReachabilityConfig :=
  .make fun handle => client handle

section
variable [Commitment]
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

instance [Commitment] : ProtocolEvent.EventInv Acceptance where
  invariant _ event := event.item = Commitment.item

section
variable [Commitment]
#combine +toplevel into SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  Network,
  ProtocolEvent Acceptance,

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Literal,
  Concat,
  Hash,

theorem client_preserves (handle : Nat) :
    HoareTriple (client handle) (fun _ => True) (fun _ _ => True) :=
  receive_preserves _ handle fun message event accepted _ =>
    Step.client_step_sound message event accepted

instance : ReachableImpliesInvariant client.reachability :=
  .mk (fun handle => client_preserves handle)

#combine into ReachabilityTheorem from
  Network,
  client,

/-- Every acceptance on a reachable trace carries the committed item, whatever the attacker
sends. -/
theorem client_authentication (event : Acceptance) (time : Nat) :
    ∀ tr : ExecTrace, tr.Reachable reachability → tr.EventLoggedAt event time →
      event.item = Commitment.item := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv logged
  exact Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged
end

end
end
end Leaf.Protocol
