module
public import Protocol

namespace Qmdb
open DY Aeneas Aeneas.Std Protocol qmdb_dylean
@[expose] public section

/-- The pinned production traversal and the Rust specification accept exactly the same openings. -/
theorem traversal_matches_spec (h : Std.U32) (loc : Std.U64) (root : Bytes) (item : ByteArray)
    (siblings : Slice Bytes) :
    adapter.verify dyTerms h loc root item siblings =
      spec.verify_single dyTerms h loc root item siblings := by
  rw [Correspondence.traversal_verify_eq, Correspondence.verify_single_eq]

/-- The Rust specification's honest root is the reference model's. -/
theorem spec_root [Snapshot] (bound : (Snapshot.height).val ≤ 63) :
    spec.root dyTerms snapshotStore () Snapshot.height =
      RustM.ok (wrap (Snapshot.height).val
        (tree Snapshot.items (Snapshot.height).val (2*(2^(Snapshot.height).val-1)) 0)) :=
  Correspondence.root_eq bound

/-- Authentication on traces consisting of attacker sends and extracted client steps. -/
theorem extracted_client_authentication [Snapshot] (event : Acceptance) (t : Nat)
    (tr : ExecTrace) (reachable : tr.Reachable reachability)
    (accepted : tr.EventLoggedAt event t) :
    event.height = Snapshot.height ∧ event.location.val < 2^event.height.val ∧
      event.item = Snapshot.items event.location.val :=
  client_authentication event t tr reachable accepted

#print axioms traversal_matches_spec
#print axioms spec_root
#print axioms extracted_client_authentication
end
end Qmdb
