module
public import Protocol
public import Correspondence

namespace Qmdb
open DY Protocol
@[expose] public section

instance extractedVerifier : Verifier where
  verify := Bridge.verify
  sound := fun h loc root item ws => (Bridge.verify_iff h loc root item ws).mp

/-- The model and extracted checkers induce identical client actions, including
the traces exercised by the executable sanity checks. -/
theorem same_verifier : extractedVerifier = modelVerifier := by
  have eq : Bridge.verify = check := by
    funext h loc root item ws
    apply Bool.eq_iff_iff.mpr
    exact (Bridge.verify_iff ..).trans (check_spec ..).symm
  unfold extractedVerifier modelVerifier
  congr

/-- Authentication on traces consisting of attacker sends and client verification steps. -/
theorem extracted_client_authentication [Snapshot] (h loc : Nat) (item : ByteArray) (t : Nat)
    (tr : ExecTrace) (reachable : tr.Reachable reachability)
    (accepted : tr.EventLoggedAt (Acceptance.mk h loc item) t) :
    h = Snapshot.height ∧ loc < 2^h ∧ item = Snapshot.items loc :=
  client_authentication h loc item t tr reachable accepted

#print axioms same_verifier
#print axioms extracted_client_authentication
end
end Qmdb
