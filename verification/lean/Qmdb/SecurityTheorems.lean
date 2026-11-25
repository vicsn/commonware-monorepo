module
public import Qmdb.Completeness

/-! What the QMDB target proves about the protocol and its assumption. Trusted: the three
statements. The properties of the extracted verifier are stated once, in `Inclusion`: `unique`
(accepted openings are unique, so the verifier is position binding), `verify_total`,
`verify_bounds`, `honest_opening` and `extra_sibling_rejected`. -/

namespace Qmdb
open DY Aeneas Aeneas.Std Commonware.Symbolic Protocol commonware_symbolic
@[expose] public section

/-- The snapshot assumption is satisfiable: for any items and any height that
the client accepts, some root and siblings give every stored item an opening
that the extracted verifier accepts. -/
theorem honest_snapshots_exist
    (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ Inclusion.maxHeight) :
    ∃ (root : Bytes) (siblings : Std.U64 → Slice Bytes),
      ∀ loc : Std.U64,
        loc.val < 2 ^ h.val →
        inclusion.verify_element_inclusion dyTerms () h loc root (items loc)
          (siblings loc) =
          RustM.ok true :=
  ⟨_, fun loc => Inclusion.honestSiblings items h.val loc bound,
    fun loc inside => Inclusion.honest_opening items h bound loc inside⟩

/-- Authentication on traces of attacker sends and extracted client steps: every
acceptance that the client logs names the snapshot height, an in-range location
and the item stored there. -/
theorem client_authentication
    [Snapshot]
    (event : Acceptance) (time : Nat) :
    ∀ tr : ExecTrace,
      tr.Reachable reachability →
      tr.EventLoggedAt event time →
      event.height = Snapshot.height ∧
      event.location.val < 2 ^ event.height.val ∧
      event.item = Snapshot.items event.location := by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr inv logged
  exact Trace.EventLoggedAt_imp_EventInv _ _ _ inv logged

/-- Completeness on traces: the client does log the honest acceptance. For
every location of the snapshot some reachable trace has logged the acceptance
of the item stored there, so `client_authentication` is not about an empty set
of events. -/
theorem honest_acceptance_logged
    [Snapshot]
    (loc : Std.U64) (inside : loc.val < 2 ^ Snapshot.height.val) :
    ∃ tr : ExecTrace,
      tr.Reachable reachability ∧
      ∃ time,
        tr.EventLoggedAt
          ({ height := Snapshot.height,
             location := loc,
             item := Snapshot.items loc } : Acceptance)
          time := by
  obtain ⟨time, logged⟩ := Completeness.attempt_logs (Snapshot.items loc) loc
    (Snapshot.siblings loc) _ (Symbolic.client_step_complete loc inside)
  exact ⟨_, Completeness.attempt_reachable _ loc _, time, logged⟩

end
end Qmdb
