module
public import Protocol
public import Scenarios

namespace Qmdb.Sanity
open DY Aeneas Aeneas.Std Protocol Scenarios

public def attempt (claimed : ByteArray) (loc : Std.U64) (ws : Slice Bytes) : Traceful Unit := do
  let handle ← Network.sendMessage (Literal.literalToBytes claimed)
  client handle loc ws

/-- Every scenario is a reachable protocol execution: an attacker-known literal followed by
precisely the registered client action. -/
public theorem attempt_reachable (claimed : ByteArray) (loc : Std.U64) (ws : Slice Bytes) :
    ((attempt claimed loc ws).run Trace.empty).snd.val.Reachable reachability := by
  apply Traceful.PreservesReachability_to_Reachable (pre := fun _ => True)
    (post := fun _ _ => True)
  · intro tr reachable _
    unfold attempt
    apply Traceful.PreservesReachabilityFrom_bind
    · apply Traceful.PreservesReachability_base Network.reachability
    · exact reachable
    · simp [Literal.attacker_knows_literalToBytes]
    intro handle tr _ reachable _
    apply Traceful.PreservesReachability_base client.reachability _ (handle,loc,ws)
    · exact reachable
    · trivial
  · trivial

#print axioms attempt_reachable
end Qmdb.Sanity
