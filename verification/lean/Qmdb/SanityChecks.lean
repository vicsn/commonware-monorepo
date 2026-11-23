module
public import Qmdb.SecurityTheorems

/-! A concrete two-item snapshot and the extracted client's decisions on it. -/

namespace Qmdb.Sanity
open DY Aeneas Aeneas.Std Commonware.Symbolic Protocol Verifier Symbolic commonware_symbolic
@[expose] public section

/-- ASCII `Alice`. -/
def alice : Slice Std.U8 := Slice.from [65#u8, 108#u8, 105#u8, 99#u8, 101#u8] (by scalar_tac)

/-- ASCII `Bob`. -/
def bob : Slice Std.U8 := Slice.from [66#u8, 111#u8, 98#u8] (by scalar_tac)

/-- `Alice` at location 0 and `Bob` everywhere else. -/
def items (loc : Std.U64) : Slice Std.U8 := if loc.val = 0 then alice else bob

theorem alice_ne_bob : alice ≠ bob := by
  intro same
  have := congrArg (fun s : Slice Std.U8 => s.val.length) same
  simp [alice, bob, Slice.from_val] at this

/-- The honest snapshot of `Alice` at location 0 and `Bob` at location 1. -/
instance snapshot : Snapshot where
  height := 1#u32
  root := honestRoot items 1
  items := items
  siblings loc := honestSiblings items 1 loc one_le_maxHeight
  honest loc inside := honest_opening items 1#u32 one_le_maxHeight loc inside

noncomputable section

/-- The honest siblings of `Alice` at location 0. -/
def honestAlice : Slice Bytes := honestSiblings items 1 0#u64 one_le_maxHeight

/-- The honest siblings of `Bob` at location 1. -/
def honestBob : Slice Bytes := honestSiblings items 1 1#u64 one_le_maxHeight

/-- The client step of the protocol on a message carrying `item`. -/
abbrev verdict (item : Slice Std.U8) (loc : Std.U64) (ws : Slice Bytes) :=
  qmdb.client_step dyTerms messages () Snapshot.root Snapshot.height (carrying item) loc ws

theorem accepts_alice : verdict alice 0#u64 honestAlice =
    RustM.ok (some { height := 1#u32, location := 0#u64, item := alice }) :=
  honest_accepted items 1#u32 one_le_maxHeight 0#u64 (by decide)

theorem accepts_bob : verdict bob 1#u64 honestBob =
    RustM.ok (some { height := 1#u32, location := 1#u64, item := bob }) :=
  honest_accepted items 1#u32 one_le_maxHeight 1#u64 (by decide)

/-- `Bob` claimed at Alice's location, whatever the siblings. -/
theorem rejects_substituted (ws : Slice Bytes) : verdict bob 0#u64 ws = RustM.ok none :=
  substitution_rejected items 1#u32 one_le_maxHeight 0#u64 (by decide) bob
    (by simp [items]; exact alice_ne_bob.symm) ws

/-- `Alice` claimed at Bob's location, whatever the siblings. -/
theorem rejects_misplaced (ws : Slice Bytes) : verdict alice 1#u64 ws = RustM.ok none :=
  substitution_rejected items 1#u32 one_le_maxHeight 1#u64 (by decide) alice
    (by simp [items]; exact alice_ne_bob) ws

/-- Alice's honest opening followed by one unused sibling. -/
def longAlice (extra : Bytes) : Slice Bytes :=
  Slice.from (path items 1 (2 * (2 ^ 1 - 1)) 0 0 ++ [extra])
    (by simp [path_length]; scalar_tac)

theorem rejects_long (extra : Bytes) : verdict alice 0#u64 (longAlice extra) = RustM.ok none := by
  have rejected := extra_sibling_rejected items 1#u32 one_le_maxHeight 0#u64 (by decide)
    (longAlice extra) extra (by simp [longAlice, Slice.from_val])
  have stored : items 0#u64 = alice := by simp [items]
  rw [stored] at rejected
  change qmdb.client_step dyTerms messages () (honestRoot items (1#u32 : Std.U32).val) 1#u32
    (carrying alice) 0#u64 (longAlice extra) = _
  rw [client_step_carrying, rejected]
  simp

end

end
end Qmdb.Sanity
