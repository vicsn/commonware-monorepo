module
public import Qmdb.Protocol

namespace Qmdb
open DY Aeneas Aeneas.Std Commonware.Symbolic Protocol commonware_symbolic
@[expose] public section

/-- Position binding of the production verifier over byte strings, for any hash whose digests
have a fixed-length, injective byte representation: two openings that it accepts at the same
location under the same root carry the same item, or `Verifier.finder` returns two different
byte strings with the same digest. -/
theorem production_binding_or_collision {D : Type} [DecidableEq D] (B : ByteHash D)
    (h : Std.U32) (loc : Std.U64) (root : D) (a b : Slice Std.U8) (wa wb : Slice D)
    (ha : qmdb.verify B.scheme.terms () h loc root a wa = RustM.ok true)
    (hb : qmdb.verify B.scheme.terms () h loc root b wb = RustM.ok true) :
    a = b ∨ ∃ x y : List Std.U8, Verifier.finder B.scheme h loc a b wa wb = some (x, y) ∧
      x ≠ y ∧ B.hash x = B.hash y :=
  Verifier.byte_binding_or_collision B h loc root a b wa wb ha hb

/-- Binding of the production verifier under symbolic hashing: two openings that it accepts at
the same location under the same root carry the same item. -/
theorem production_binding (h : Std.U32) (loc : Std.U64) (root : Bytes) (a b : Slice Std.U8)
    (wa wb : Slice Bytes) (ha : qmdb.verify dyTerms () h loc root a wa = RustM.ok true)
    (hb : qmdb.verify dyTerms () h loc root b wb = RustM.ok true) : a = b :=
  Symbolic.binding h loc root a b wa wb ha hb

/-- Uniqueness of the openings that the production verifier accepts over byte strings, for any
hash whose digests have a fixed-length, injective byte representation: two openings that it
accepts at the same location under the same root carry the same item and the same siblings, or
`Verifier.finder` returns two different byte strings with the same digest. -/
theorem production_unique_or_collision {D : Type} [DecidableEq D] (B : ByteHash D)
    (h : Std.U32) (loc : Std.U64) (root : D) (a b : Slice Std.U8) (wa wb : Slice D)
    (ha : qmdb.verify B.scheme.terms () h loc root a wa = RustM.ok true)
    (hb : qmdb.verify B.scheme.terms () h loc root b wb = RustM.ok true) :
    (a = b ∧ wa = wb) ∨ ∃ x y : List Std.U8, Verifier.finder B.scheme h loc a b wa wb =
      some (x, y) ∧ x ≠ y ∧ B.hash x = B.hash y :=
  Verifier.byte_unique_or_collision B h loc root a b wa wb ha hb

/-- Uniqueness of the openings that the production verifier accepts under symbolic hashing: an
accepted opening at a location under a root is the only one. -/
theorem production_unique (h : Std.U32) (loc : Std.U64) (root : Bytes) (a b : Slice Std.U8)
    (wa wb : Slice Bytes) (ha : qmdb.verify dyTerms () h loc root a wa = RustM.ok true)
    (hb : qmdb.verify dyTerms () h loc root b wb = RustM.ok true) : a = b ∧ wa = wb :=
  Symbolic.unique h loc root a b wa wb ha hb

/-- The snapshot assumption is satisfiable under every hash: for any items and height up to 62,
some root and siblings give every stored item an opening that the production verifier accepts. -/
theorem honest_snapshots_exist (hash : Bytes → Bytes) (items : Std.U64 → Slice Std.U8)
    (h : Std.U32) (bound : h.val ≤ 62) :
    ∃ (root : Bytes) (siblings : Std.U64 → Slice Bytes), ∀ loc : Std.U64, loc.val < 2^h.val →
      qmdb.verify (hashing hash).terms () h loc root (items loc) (siblings loc) = RustM.ok true :=
  ⟨_, fun loc => Verifier.honestSiblings (hashing hash) items h.val loc bound,
    fun loc inside => Verifier.honest_opening (hashing hash) items h bound loc inside⟩

/-- Authentication on traces consisting of attacker sends and extracted client steps, under the
snapshot's hash, which may collide: a logged opening names the snapshot height and an in-range
location, and its item is the one stored there or `Verifier.finder` returns two different hash
inputs with the same digest, from the logged opening and the snapshot's. -/
theorem extracted_client_authentication [Snapshot] (opened : Opened) (t : Nat)
    (tr : ExecTrace) (reachable : tr.Reachable reachability)
    (logged : tr.EventLoggedAt opened t) :
    opened.acceptance.height = Snapshot.height ∧
    opened.acceptance.location.val < 2^opened.acceptance.height.val ∧
    (opened.acceptance.item = Snapshot.items opened.acceptance.location ∨
      ∃ x y, Verifier.finder Snapshot.scheme opened.acceptance.height opened.acceptance.location
        opened.acceptance.item (Snapshot.items opened.acceptance.location) opened.siblings
        (Snapshot.siblings opened.acceptance.location) = some (x, y) ∧
        x ≠ y ∧ Snapshot.hash x = Snapshot.hash y) :=
  client_authentication opened t tr reachable logged

/-- Authentication with a hash that has no collisions, such as DyLean's constructor: a logged
opening names the snapshot height, an in-range location and the item stored there. -/
theorem collision_free_client_authentication [Snapshot]
    (free : ∀ x y : Bytes, Snapshot.hash x = Snapshot.hash y → x = y) (opened : Opened) (t : Nat)
    (tr : ExecTrace) (reachable : tr.Reachable reachability)
    (logged : tr.EventLoggedAt opened t) :
    opened.acceptance.height = Snapshot.height ∧
    opened.acceptance.location.val < 2^opened.acceptance.height.val ∧
    opened.acceptance.item = Snapshot.items opened.acceptance.location :=
  collision_free_authentication free opened t tr reachable logged

end
end Qmdb
