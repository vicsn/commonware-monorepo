module
public import Binding
public import DY.Actions.Network
public import DY.Actions.ProtocolEvent
import DY.Meta

namespace Qmdb.Protocol
open DY
@[expose] public section

structure Acceptance where
  height : Nat
  location : Nat
  item : ByteArray

-- A fixed, authenticated historical snapshot supplied by the application.
class Snapshot where
  items : Nat → ByteArray
  height : Nat

#combine +toplevel into ExecEntryT, baseAttackerKnowledge from
  Network,
  ProtocolEvent Acceptance,

def check (h loc : Nat) (root : Bytes) (item : ByteArray) (ws : List Bytes) : Bool :=
  h ≤ 63 && loc < 2^h &&
    match replay item h (2*(2^h-1)) 0 loc ws with
    | some (peak,[]) => decide (wrap h peak = root)
    | _ => false

theorem check_spec (h loc : Nat) (root : Bytes) (item : ByteArray) (ws : List Bytes) :
    check h loc root item ws = true ↔ accepts h loc root item ws := by
  unfold check accepts
  cases hr : replay item h (2*(2^h-1)) 0 loc ws with
  | none => simp
  | some pair => obtain ⟨p,rest⟩ := pair; cases rest <;> simp [and_assoc]

class Verifier where
  verify : Nat → Nat → Bytes → ByteArray → List Bytes → Bool
  sound : ∀ h loc root item ws, verify h loc root item ws = true → accepts h loc root item ws

@[instance_reducible] def modelVerifier : Verifier where
  verify := check
  sound := fun h loc root item ws => (check_spec h loc root item ws).mp

def client [Snapshot] [Verifier] (handle loc : Nat) (ws : List Bytes) : Traceful Unit := do
  let message ← Network.receiveMessage handle
  let some item := Literal.bytesToLiteral message | failure
  let h := Snapshot.height
  let root := wrap h (tree Snapshot.items h (2*(2^h-1)) 0)
  guard (Verifier.verify h loc root item ws)
  ProtocolEvent.logEvent (Acceptance.mk h loc item)

def client.reachability [Snapshot] [Verifier] : ReachabilityConfig :=
  .make fun (handle,loc,ws) => client handle loc ws

section
variable [Snapshot] [Verifier]
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
  invariant _ event := event.height = Snapshot.height ∧ event.location < 2^event.height ∧ event.item = Snapshot.items event.location

section
variable [Snapshot] [Verifier]
#combine +toplevel into SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  Network,
  ProtocolEvent Acceptance,

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Literal,
  Concat,
  Hash,

theorem client_preserves (handle loc : Nat) (ws : List Bytes) :
    HoareTriple (client handle loc ws) (fun _ => True) (fun _ _ => True) := by
  unfold client
  step
  split
  · dsimp only
    step
    step by
      simp only [ProtocolEvent.EventInv.invariant, true_and]
      have accepted := Verifier.sound _ _ _ _ _ (by assumption)
      exact ⟨accepted.2.1, inclusion_sound _ _ _ _ _ accepted⟩
    trivial
  · step

instance : ReachableImpliesInvariant client.reachability :=
  .mk (fun (handle,loc,ws) => client_preserves handle loc ws)

#combine into ReachabilityTheorem from
  Network,
  client,

theorem client_authentication (h loc : Nat) (item : ByteArray) (time : Nat) :
    ∀ tr : ExecTrace, tr.Reachable reachability →
      tr.EventLoggedAt (Acceptance.mk h loc item) time →
      h = Snapshot.height ∧ loc < 2^h ∧ item = Snapshot.items loc := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv event
  exact Trace.EventLoggedAt_imp_EventInv _ _ _ inv event
end
end
end Qmdb.Protocol
