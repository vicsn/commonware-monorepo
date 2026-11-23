module
public import Qmdb.Protocol

/-! What the QMDB target proves about the protocol and its assumption. Trusted: the two
statements. The properties of the extracted verifier are stated once, in `Verifier`: `unique`
(accepted openings are unique, so the verifier is position binding), `verify_total`,
`verify_bounds`, `honest_opening` and `extra_sibling_rejected`. -/

namespace Qmdb
open DY Aeneas Aeneas.Std Commonware.Symbolic Protocol commonware_symbolic
@[expose] public section

/-- The snapshot assumption is satisfiable: for any items and any height that the client accepts,
some root and siblings give every stored item an opening that the extracted verifier accepts. -/
theorem honest_snapshots_exist (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ Verifier.maxHeight) :
    ∃ (root : Bytes) (siblings : Std.U64 → Slice Bytes), ∀ loc : Std.U64, loc.val < 2^h.val →
      qmdb.verify dyTerms () h loc root (items loc) (siblings loc) = RustM.ok true :=
  ⟨_, fun loc => Verifier.honestSiblings items h.val loc bound,
    fun loc inside => Verifier.honest_opening items h bound loc inside⟩

/-- Authentication on traces of attacker sends and extracted client steps: every acceptance that
the client logs names the snapshot height, an in-range location and the item stored there. -/
theorem client_authentication [Snapshot] (event : Acceptance) (time : Nat) :
    ∀ tr : ExecTrace, tr.Reachable reachability → tr.EventLoggedAt event time →
      event.height = Snapshot.height ∧ event.location.val < 2^event.height.val ∧
      event.item = Snapshot.items event.location := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv logged
  exact Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged

end
end Qmdb
