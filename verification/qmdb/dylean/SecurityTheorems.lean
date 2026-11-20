module
public import Protocol

namespace Qmdb
open DY Aeneas Aeneas.Std Protocol qmdb_dylean
@[expose] public section

/-- Position binding of the production verifier over byte strings, for any hash whose digests
have a fixed-length, injective byte representation: two openings that it accepts at the same
location under the same root carry the same item, or `Verifier.finder` returns two different
byte strings with the same digest. -/
theorem production_binding_or_collision {D : Type} [DecidableEq D] (B : ByteHash D)
    (h : Std.U32) (loc : Std.U64) (root : D) (a b : Slice Std.U8) (wa wb : Slice D)
    (ha : client.verify B.scheme.terms () h loc root a wa = RustM.ok true)
    (hb : client.verify B.scheme.terms () h loc root b wb = RustM.ok true) :
    a = b ∨ ∃ x y : List Std.U8, Verifier.finder B.scheme h loc a b wa wb = some (x, y) ∧
      x ≠ y ∧ B.hash x = B.hash y :=
  Verifier.byte_binding_or_collision B h loc root a b wa wb ha hb

/-- Binding of the production verifier under symbolic hashing: two openings that it accepts at
the same location under the same root carry the same item. -/
theorem production_binding (h : Std.U32) (loc : Std.U64) (root : Bytes) (a b : Slice Std.U8)
    (wa wb : Slice Bytes) (ha : client.verify dyTerms () h loc root a wa = RustM.ok true)
    (hb : client.verify dyTerms () h loc root b wb = RustM.ok true) : a = b :=
  Symbolic.binding h loc root a b wa wb ha hb

/-- The snapshot assumption is satisfiable: for any items and height up to 62, some root gives
every stored item an opening that the production verifier accepts. -/
theorem honest_snapshots_exist (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ 62) :
    ∃ root : Bytes, ∀ loc : Std.U64, loc.val < 2^h.val → ∃ ws : Slice Bytes,
      client.verify dyTerms () h loc root (items loc) ws = RustM.ok true :=
  ⟨_, fun loc inside => ⟨_, Verifier.honest_opening symbolic items h bound loc inside⟩⟩

/-- Authentication on traces consisting of attacker sends and extracted client steps. -/
theorem extracted_client_authentication [Snapshot] (event : Acceptance) (t : Nat)
    (tr : ExecTrace) (reachable : tr.Reachable reachability)
    (accepted : tr.EventLoggedAt event t) :
    event.height = Snapshot.height ∧ event.location.val < 2^event.height.val ∧
      event.item = Snapshot.items event.location :=
  client_authentication event t tr reachable accepted

#print axioms production_binding_or_collision
#print axioms production_binding
#print axioms honest_snapshots_exist
#print axioms extracted_client_authentication
end
end Qmdb
