module
public import Protocol

namespace Qmdb
open DY Aeneas Aeneas.Std Protocol qmdb_dylean
@[expose] public section

/-- Binding of the production verifier: two openings that it accepts at the same location
under the same root carry the same item. -/
theorem production_binding (h : Std.U32) (loc : Std.U64) (root : Bytes) (a b : ByteArray)
    (wa wb : Slice Bytes) (ha : adapter.verify dyTerms h loc root a wa = RustM.ok true)
    (hb : adapter.verify dyTerms h loc root b wb = RustM.ok true) : a = b :=
  Correspondence.binding h loc root a b wa wb ha hb

/-- The snapshot assumption is satisfiable: for any items and height up to 63, some root gives
every stored item an opening that the production verifier accepts. -/
theorem honest_snapshots_exist (items : Nat → ByteArray) (h : Std.U32) (bound : h.val ≤ 63) :
    ∃ root : Bytes, ∀ loc : Std.U64, loc.val < 2^h.val → ∃ ws : Slice Bytes,
      adapter.verify dyTerms h loc root (items loc.val) ws = RustM.ok true :=
  ⟨_, Correspondence.honest_opening_accepted items h bound⟩

/-- Authentication on traces consisting of attacker sends and extracted client steps. -/
theorem extracted_client_authentication [Snapshot] (event : Acceptance) (t : Nat)
    (tr : ExecTrace) (reachable : tr.Reachable reachability)
    (accepted : tr.EventLoggedAt event t) :
    event.height = Snapshot.height ∧ event.location.val < 2^event.height.val ∧
      event.item = Snapshot.items event.location.val :=
  client_authentication event t tr reachable accepted

#print axioms production_binding
#print axioms honest_snapshots_exist
#print axioms extracted_client_authentication
end
end Qmdb
