module
public import Reference
public meta import Reference

/-! Executable client decisions on a two-item snapshot. `Correspondence.client_step_eq` makes the
extracted Rust decision equal to `Reference.step`, so these outcomes are the extracted client's.
`SanityChecks` proves the corresponding protocol traces reachable. -/

namespace Qmdb.Scenarios
open DY Aeneas Aeneas.Std
@[expose] public section

def alice := "Alice".toUTF8
def bob := "Bob".toUTF8

instance snapshot : Snapshot where
  height := 1#u32
  items := fun i => if i = 0 then alice else bob

def opening (ws : List Bytes) (short : ws.length ≤ 2 := by decide) : Slice Bytes :=
  Slice.from ws (by scalar_tac)

/-- Claimed item, location, opening and expected verdict: two honest openings, then a
substituted item, a misplaced item, a short opening and a long opening. -/
def claims : List (ByteArray × Std.U64 × Slice Bytes × Bool) :=
  let sibling := leaf 1 bob
  [(alice, 0#u64, opening [sibling], true), (bob, 1#u64, opening [leaf 0 alice], true),
    (bob, 0#u64, opening [sibling], false), (alice, 1#u64, opening [sibling], false),
    (alice, 0#u64, opening [], false), (alice, 0#u64, opening [sibling, sibling], false)]

def testRuns : IO Unit := do
  for (claim, loc, ws, valid) in claims do
    let accepted := (Reference.step (Literal.literalToBytes claim) loc ws).isSome
    unless accepted == valid do throw (IO.userError "unexpected client decision")

end
end Qmdb.Scenarios
public def main := Qmdb.Scenarios.testRuns
