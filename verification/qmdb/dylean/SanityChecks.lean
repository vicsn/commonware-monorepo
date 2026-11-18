module
public import Protocol
public meta import Protocol

namespace Qmdb.Sanity
open DY Protocol

private instance : Verifier := modelVerifier

private def alice := "Alice".toUTF8
private def bob := "Bob".toUTF8
private instance : Snapshot where
  height := 1
  items := fun i => if i = 0 then alice else bob

private def attempt (claimed : ByteArray) (loc : Nat) (ws : List Bytes) : Traceful Unit := do
  let handle ← Network.sendMessage (Literal.literalToBytes claimed)
  client handle loc ws

-- Each execution starts with an attacker-known literal, then uses precisely
-- the registered client action. A successful action appends its acceptance event.
private theorem attempt_reachable (claimed : ByteArray) (loc : Nat) (ws : List Bytes) :
    ((attempt claimed loc ws).run Trace.empty).snd.val.Reachable reachability := by
  apply Traceful.PreservesReachability_to_Reachable (pre := fun _ => True) (post := fun _ _ => True)
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

public def testRuns : IO Unit := do
  let sibling := leaf 1 bob
  for (claim, loc, ws, valid) in [(alice,0,[sibling],true), (bob,1,[leaf 0 alice],true),
      (bob,0,[sibling],false), (alice,1,[sibling],false), (alice,0,[],false),
      (alice,0,[sibling,sibling],false)] do
    let tr := ((attempt claim loc ws).run Trace.empty).snd.val
    let logged := (tr.getEventAt (EventT := Acceptance) 1).isSome
    unless logged == valid do throw (IO.userError "unexpected client acceptance event")
end Qmdb.Sanity
public def main := Qmdb.Sanity.testRuns
