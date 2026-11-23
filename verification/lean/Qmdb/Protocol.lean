module
public import Qmdb.Symbolic
public import Commonware.Symbolic.Client
import DY.Meta

/-! The DyLean protocol around the extracted QMDB client. Trusted: `client`, the event invariant
and the `#combine` configuration. The client is the shared `Commonware.Symbolic.receive` action
over the extracted `client_step`, so preservation of the trace invariant reduces to
`Symbolic.client_step_sound`. `SecurityTheorems` states what follows on reachable traces. -/

namespace Qmdb.Protocol
open DY Aeneas Aeneas.Std Commonware.Symbolic
@[expose] public section

abbrev Acceptance := commonware_symbolic.qmdb.Acceptance

#combine +toplevel into ExecEntryT, baseAttackerKnowledge from
  Network,
  ProtocolEvent Acceptance,

noncomputable section

/-- Receive a claimed item and log the acceptance that the extracted Rust decision returns. -/
def client [Snapshot] (handle : Nat) (loc : Std.U64) (ws : Slice Bytes) : Traceful Unit :=
  receive (fun message => commonware_symbolic.qmdb.client_step dyTerms messages ()
    Snapshot.root Snapshot.height message loc ws) handle

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
    event.location.val < 2^event.height.val ∧ event.item = Snapshot.items event.location

section
variable [Snapshot]
#combine +toplevel into SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  Network,
  ProtocolEvent Acceptance,

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Literal,
  Concat,
  Hash,

theorem client_preserves (handle : Nat) (loc : Std.U64) (ws : Slice Bytes) :
    HoareTriple (client handle loc ws) (fun _ => True) (fun _ _ => True) :=
  receive_preserves _ handle fun message event accepted _ =>
    Symbolic.client_step_sound message loc ws event accepted

instance : ReachableImpliesInvariant client.reachability :=
  .mk (fun (handle, loc, ws) => client_preserves handle loc ws)

#combine into ReachabilityTheorem from
  Network,
  client,
end

end
end
end Qmdb.Protocol
