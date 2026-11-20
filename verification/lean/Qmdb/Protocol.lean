module
public import Qmdb.Symbolic
public import Commonware.Symbolic.Client
import DY.Meta

/-! The DyLean protocol around the extracted QMDB client, under the snapshot's hash, which may
collide. Trusted: `Opened`, `client`, the event invariant, the `#combine` configuration and the
theorem statements. The client is the shared `Commonware.Symbolic.receive` action over the
extracted `client_step`, so preservation of the trace invariant reduces to
`Symbolic.client_step_sound`. -/

namespace Qmdb.Protocol
open DY Aeneas Aeneas.Std Commonware.Symbolic
@[expose] public section

abbrev Acceptance := commonware_symbolic.qmdb.Acceptance

/-- What the client logs: the acceptance that the extracted step returns and the siblings that
the client was given. -/
structure Opened where
  acceptance : Acceptance
  siblings : Slice Bytes

#combine +toplevel into ExecEntryT, baseAttackerKnowledge from
  Network,
  ProtocolEvent Opened,

noncomputable section

/-- Receive a claimed item and log the acceptance that the extracted Rust decision returns,
together with the siblings it was decided on. -/
def client [Snapshot] (handle : Nat) (loc : Std.U64) (ws : Slice Bytes) : Traceful Unit :=
  receive (fun message => do
    let accepted ← commonware_symbolic.qmdb.client_step Snapshot.scheme.terms messages ()
      Snapshot.root Snapshot.height message loc ws
    RustM.ok (match accepted with
      | some acceptance => some (Opened.mk acceptance ws)
      | none => none)) handle

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
  ProtocolEvent Opened,

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Literal,
  Concat,
  Hash,

instance [Snapshot] : ProtocolEvent.EventInv Opened where
  invariant _ opened := opened.acceptance.height = Snapshot.height ∧
    opened.acceptance.location.val < 2^opened.acceptance.height.val ∧
    (opened.acceptance.item = Snapshot.items opened.acceptance.location ∨
      ∃ x y, Verifier.finder Snapshot.scheme opened.acceptance.height opened.acceptance.location
        opened.acceptance.item (Snapshot.items opened.acceptance.location) opened.siblings
        (Snapshot.siblings opened.acceptance.location) = some (x, y) ∧
        x ≠ y ∧ Snapshot.hash x = Snapshot.hash y)

section
variable [Snapshot]
#combine +toplevel into SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  Network,
  ProtocolEvent Opened,

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Literal,
  Concat,
  Hash,

theorem client_preserves (handle : Nat) (loc : Std.U64) (ws : Slice Bytes) :
    HoareTriple (client handle loc ws) (fun _ => True) (fun _ _ => True) :=
  receive_preserves _ handle fun message opened logged _ => by
    obtain ⟨accepted, step, wrapped⟩ := bind_eq_ok logged
    cases accepted with
    | none => simpa using ok_inj wrapped
    | some acceptance =>
      have same := ok_inj wrapped
      simp at same
      subst same
      exact Symbolic.client_step_sound message loc ws acceptance step

instance : ReachableImpliesInvariant client.reachability :=
  .mk (fun (handle, loc, ws) => client_preserves handle loc ws)

#combine into ReachabilityTheorem from
  Network,
  client,

/-- Every opening logged on a reachable trace names the snapshot height and an in-range location,
and its item is the one stored there or `Verifier.finder` returns two different hash inputs with
the same digest, from the logged opening and the snapshot's. -/
theorem client_authentication (opened : Opened) (time : Nat) :
    ∀ tr : ExecTrace, tr.Reachable reachability → tr.EventLoggedAt opened time →
      opened.acceptance.height = Snapshot.height ∧
      opened.acceptance.location.val < 2^opened.acceptance.height.val ∧
      (opened.acceptance.item = Snapshot.items opened.acceptance.location ∨
        ∃ x y, Verifier.finder Snapshot.scheme opened.acceptance.height
          opened.acceptance.location opened.acceptance.item
          (Snapshot.items opened.acceptance.location) opened.siblings
          (Snapshot.siblings opened.acceptance.location) = some (x, y) ∧
          x ≠ y ∧ Snapshot.hash x = Snapshot.hash y) := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv logged
  exact Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged

/-- With a hash that has no collisions, such as DyLean's constructor, every opening logged on a
reachable trace names the snapshot height, an in-range location and the item stored there. -/
theorem collision_free_authentication
    (free : ∀ x y : Bytes, Snapshot.hash x = Snapshot.hash y → x = y) (opened : Opened)
    (time : Nat) :
    ∀ tr : ExecTrace, tr.Reachable reachability → tr.EventLoggedAt opened time →
      opened.acceptance.height = Snapshot.height ∧
      opened.acceptance.location.val < 2^opened.acceptance.height.val ∧
      opened.acceptance.item = Snapshot.items opened.acceptance.location := by
  intro tr reachable logged
  obtain ⟨height, inside, same | ⟨x, y, -, differ, clash⟩⟩ :=
    client_authentication opened time tr reachable logged
  · exact ⟨height, inside, same⟩
  · exact absurd (free x y clash) differ
end

end
end
end Qmdb.Protocol
