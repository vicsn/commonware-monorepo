module
public import Qmdb.Protocol
meta import Commonware.Symbolic.Hashing
meta import Qmdb.Verifier

/-! A concrete two-item snapshot, the extracted client's decisions on it, and reachability of the
protocol traces that carry those decisions. Then two hashes that collide, for which the collision
finder returns a collision: one between two leaf inputs when the items differ, one between two
node inputs when only a sibling differs. The client's decisions are proved; the finder is also
executed. -/

namespace Qmdb.Sanity
open DY Aeneas Aeneas.Std Commonware.Symbolic Protocol Verifier Symbolic commonware_symbolic
@[expose] public section

/-- ASCII `Alice`. -/
def alice : Slice Std.U8 := Slice.from [65#u8, 108#u8, 105#u8, 99#u8, 101#u8] (by scalar_tac)

/-- ASCII `Bob`. -/
def bob : Slice Std.U8 := Slice.from [66#u8, 111#u8, 98#u8] (by scalar_tac)

def items (loc : Std.U64) : Slice Std.U8 := if loc.val = 0 then alice else bob

theorem alice_ne_bob : alice ≠ bob := by
  intro same
  have := congrArg (fun s : Slice Std.U8 => s.val.length) same
  simp [alice, bob, Slice.from_val] at this

/-- The honest snapshot of `Alice` at location 0 and `Bob` at location 1. -/
instance snapshot : Snapshot where
  height := 1#u32
  root := honestRoot symbolic items 1
  items := items
  honest loc inside := ⟨_, honest_opening symbolic items 1#u32 (by decide) loc inside⟩

noncomputable section

def honestAlice : Slice Bytes := honestSiblings symbolic items 1 0#u64 (by decide)
def honestBob : Slice Bytes := honestSiblings symbolic items 1 1#u64 (by decide)

/-- The client step of the protocol on a message carrying `item`. -/
abbrev verdict (item : Slice Std.U8) (loc : Std.U64) (ws : Slice Bytes) :=
  qmdb.client_step dyTerms messages () Snapshot.root Snapshot.height (carrying item) loc ws

theorem accepts_alice : verdict alice 0#u64 honestAlice =
    RustM.ok (some { height := 1#u32, location := 0#u64, item := alice }) :=
  honest_accepted items 1#u32 (by decide) 0#u64 (by decide)

theorem accepts_bob : verdict bob 1#u64 honestBob =
    RustM.ok (some { height := 1#u32, location := 1#u64, item := bob }) :=
  honest_accepted items 1#u32 (by decide) 1#u64 (by decide)

/-- `Bob` claimed at Alice's location, whatever the siblings. -/
theorem rejects_substituted (ws : Slice Bytes) : verdict bob 0#u64 ws = RustM.ok none :=
  substitution_rejected items 1#u32 (by decide) 0#u64 (by decide) bob
    (by simp [items]; exact alice_ne_bob.symm) ws

/-- `Alice` claimed at Bob's location, whatever the siblings. -/
theorem rejects_misplaced (ws : Slice Bytes) : verdict alice 1#u64 ws = RustM.ok none :=
  substitution_rejected items 1#u32 (by decide) 1#u64 (by decide) alice
    (by simp [items]; exact alice_ne_bob) ws

/-- Alice's honest opening followed by one unused sibling. -/
def longAlice (extra : Bytes) : Slice Bytes :=
  Slice.from (path symbolic items 1 (2*(2^1-1)) 0 0 ++ [extra])
    (by simp [path_length]; scalar_tac)

theorem rejects_long (extra : Bytes) : verdict alice 0#u64 (longAlice extra) = RustM.ok none := by
  have rejected := extra_sibling_rejected symbolic items 1#u32 (by decide) 0#u64 (by decide)
    (longAlice extra) extra (by simp [longAlice, Slice.from_val])
  have stored : items 0#u64 = alice := by simp [items]
  rw [stored] at rejected
  show qmdb.client_step dyTerms messages () (honestRoot symbolic items (1#u32 : Std.U32).val) 1#u32
    (carrying alice) 0#u64 (longAlice extra) = _
  rw [client_step_carrying, rejected]
  simp

end

/-- An attacker-known message carrying `item`, followed by the registered client action. -/
noncomputable def attempt (item : Slice Std.U8) (loc : Std.U64) (ws : Slice Bytes) :
    Traceful Unit := do
  let handle ← Network.sendMessage (carrying item)
  client handle loc ws

/-- Every attempt is a reachable protocol execution. -/
theorem attempt_reachable (item : Slice Std.U8) (loc : Std.U64) (ws : Slice Bytes) :
    ((attempt item loc ws).run Trace.empty).snd.val.Reachable reachability := by
  apply Traceful.PreservesReachability_to_Reachable (pre := fun _ => True)
    (post := fun _ _ => True)
  · intro tr reachable _
    unfold attempt
    apply Traceful.PreservesReachabilityFrom_bind
    · apply Traceful.PreservesReachability_base Network.reachability
    · exact reachable
    · simp [carrying, Literal.attacker_knows_literalToBytes]
    intro handle tr _ reachable _
    apply Traceful.PreservesReachability_base client.reachability _ (handle, loc, ws)
    · exact reachable
    · trivial
  · trivial

/-! ## A hash that collides -/

/-- A hash with one digest, so that any two different byte strings collide. -/
def constant : ByteHash Unit where
  hash _ := ()
  bytes _ := []
  size := 0
  bytes_length _ := rfl
  bytes_inj _ _ _ := rfl

/-- Under the constant hash, honest openings of two snapshots that differ at a location verify
under the same root, and the finder returns two different byte strings with that digest. -/
theorem finder_finds (first second : Std.U64 → Slice Std.U8) (h : Std.U32) (bound : h.val ≤ 62)
    (loc : Std.U64) (inside : loc.val < 2^h.val) (differ : first loc ≠ second loc) :
    ∃ x y, finder constant.scheme h loc (first loc) (second loc)
      (honestSiblings constant.scheme first h.val loc bound)
      (honestSiblings constant.scheme second h.val loc bound) = some (x, y) ∧ x ≠ y := by
  have one := honest_opening constant.scheme first h bound loc inside
  have two := honest_opening constant.scheme second h bound loc inside
  rcases byte_binding_or_collision constant h loc () _ _ _ _ one two with
    same | ⟨x, y, found, clash⟩
  · exact absurd same differ
  · exact ⟨x, y, found, clash.1⟩

def values (bytes : List Std.U8) : List Nat := bytes.map fun byte => byte.val

def sibling : Slice Unit := Slice.from [()] (by scalar_tac)

-- Executed: for `Alice` and `Bob` at location 0 of a two-leaf tree, the root and node inputs
-- agree and the finder returns the two leaf inputs, each the position followed by the item.
#guard (finder constant.scheme 1#u32 0#u64 alice bob sibling sibling).map
    (fun found => (values found.1, values found.2)) ==
  some ([0, 0, 0, 0, 0, 0, 0, 0, 65, 108, 105, 99, 101], [0, 0, 0, 0, 0, 0, 0, 0, 66, 111, 98])

-- Executed: one item claimed twice gives no collision.
#guard (finder constant.scheme 1#u32 0#u64 alice alice sibling sibling).isNone

/-! ## Openings that differ in a sibling -/

/-- A hash with two digests that only tells 13-byte inputs from the others. The leaf input of
`Alice` is 13 bytes long, so a leaf holding `Alice` hashes apart from one holding `Bob`, while all
node inputs collide and so do all root inputs. -/
def coarse : ByteHash Bool where
  hash bytes := decide (bytes.length = 13)
  bytes digest := [if digest then 1#u8 else 0#u8]
  size := 1
  bytes_length _ := rfl
  bytes_inj := by decide

/-- The snapshot that stores `Alice` at every location. -/
def twins (_ : Std.U64) : Slice Std.U8 := alice

/-- Under the coarse hash, the honest openings of `Alice` at location 0 in two snapshots that
store different items at location 1 verify under the same root with different siblings, and the
finder returns two different byte strings with that digest. -/
theorem finder_finds_sibling :
    ∃ x y, finder coarse.scheme 1#u32 0#u64 alice alice
      (honestSiblings coarse.scheme twins 1 0#u64 (by decide))
      (honestSiblings coarse.scheme items 1 0#u64 (by decide)) = some (x, y) ∧ x ≠ y := by
  have root (h : Nat) : honestRoot coarse.scheme items h = honestRoot coarse.scheme twins h := by
    simp [honestRoot, rootInput, ByteHash.scheme, coarse, be_length, Array.val_to_slice]
  have differ : honestSiblings coarse.scheme twins 1 0#u64 (by decide) ≠
      honestSiblings coarse.scheme items 1 0#u64 (by decide) := by
    intro same
    have lists := congrArg (fun s : Slice Bool => s.val) same
    simp [honestSiblings, Slice.from_val, path, tree, leafInput, ByteHash.scheme, coarse,
      be_length, twins, items, alice, bob, pos] at lists
    split at lists
    · rename_i zero
      exact absurd zero (by decide)
    · simp [Slice.from_val] at lists
  have one := honest_opening coarse.scheme twins 1#u32 (by decide) 0#u64 (by decide)
  have two := honest_opening coarse.scheme items 1#u32 (by decide) 0#u64 (by decide)
  have stored : items 0#u64 = alice := by simp [items]
  rw [stored, root] at two
  rcases byte_unique_or_collision coarse 1#u32 0#u64 _ alice alice _ _ one two with
    ⟨-, same⟩ | ⟨x, y, found, clash⟩
  · exact absurd same differ
  · exact ⟨x, y, found, clash.1⟩

-- Executed: for those two openings of `Alice` the root inputs agree and the finder returns the
-- two node inputs, each the position, the digest of Alice's leaf and a sibling.
#guard (finder coarse.scheme 1#u32 0#u64 alice alice
      (honestSiblings coarse.scheme twins 1 0#u64 (by decide))
      (honestSiblings coarse.scheme items 1 0#u64 (by decide))).map
    (fun found => (values found.1, values found.2)) ==
  some ([0, 0, 0, 0, 0, 0, 0, 2, 1, 1], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0])

end
end Qmdb.Sanity
