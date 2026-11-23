module
public import Qmdb.Assumptions

/-! Logical state obtained by replaying an ordered QMDB journal in location order. -/

namespace Qmdb.Ordered
@[expose] public section

/-- Ordered journal operations, with the successor stored in each update. -/
inductive Operation (K V : Type) where
  /-- Write a value and the next active key. -/
  | update (key : K) (value : V) (next : K)
  /-- Remove the key. -/
  | delete (key : K)
  /-- Record the inactivity floor and optional metadata. -/
  | commit (metadata : Option V) (floor : UInt64)

/-- A write to the queried key, distinguishing deletion from an unrelated operation. -/
def Operation.write [DecidableEq K] (key : K) : Operation K V → Option (Option V)
  | .update k v _ => if k = key then some (some v) else none
  | .delete k => if k = key then some none else none
  | .commit .. => none

/-- The value after replaying locations strictly below the supplied bound. -/
def replay [DecidableEq K] (entry : Nat → Operation K V) (key : K) : Nat → Option V
  | 0 => none
  | n + 1 => ((entry n).write key).getD (replay entry key n)

/-- No operation between this location and the end of the snapshot touches the key. -/
def Latest [DecidableEq K] (entry : Nat → Operation K V) (key : K) (loc endLoc : Nat) : Prop :=
  ∀ i, loc < i → i < endLoc → (entry i).write key = none

/-- A later overwrite or deletion supersedes every previous write. -/
theorem replay_of_latest [DecidableEq K] {entry : Nat → Operation K V} {key : K}
    {loc endLoc : Nat} {value : Option V} (inside : loc < endLoc)
    (writes : (entry loc).write key = some value) (last : Latest entry key loc endLoc) :
    replay entry key endLoc = value := by
  induction endLoc with
  | zero => omega
  | succ n ih =>
    by_cases h : loc = n
    · subst n
      simp [replay, writes]
    · have less : loc < n := by omega
      have clear := last n less (by omega)
      simpa [replay, clear] using ih less (fun i a b => last i a (by omega))

/-- A present value is witnessed by a latest update at an in-bounds location. -/
theorem latest_of_replay [DecidableEq K] {entry : Nat → Operation K V} {key : K}
    {value : V} {endLoc : Nat} (present : replay entry key endLoc = some value) :
    ∃ loc next, loc < endLoc ∧ entry loc = .update key value next ∧
      Latest entry key loc endLoc := by
  induction endLoc with
  | zero => simp [replay] at present
  | succ n ih =>
    cases h : (entry n).write key with
    | none =>
      obtain ⟨loc, next, inside, same, last⟩ := ih (by simpa [replay, h] using present)
      exact ⟨loc, next, by omega, same, fun i a b => by
        by_cases hi : i = n
        · simpa [hi] using h
        · exact last i a (by omega)⟩
    | some write =>
      have eq : write = some value := by simpa [replay, h] using present
      subst write
      cases hop : entry n with
      | update k v next =>
        by_cases same : k = key
        · subst k
          simp [hop, Operation.write] at h
          subst v
          exact ⟨n, next, by omega, hop, fun _ _ _ => by omega⟩
        · simp [hop, Operation.write, same] at h
      | delete k => by_cases same : k = key <;> simp [hop, Operation.write, same] at h
      | commit => simp [hop, Operation.write] at h

/-- Rust's explicit inequality and `contains_cyclic(start..stop, key)` check. -/
def inGap [LinearOrder K] (start stop key : K) : Bool :=
  decide (start ≠ key) && if stop ≤ start then decide (start ≤ key ∨ key < stop)
    else decide (start ≤ key ∧ key < stop)

/-- The endpoint combination in the interval check is the extracted Rust decision. -/
theorem extracted_inGap [LinearOrder K] (start stop key : K) :
    (do
      if start = key then Aeneas.Std.RustM.ok false else
        commonware_symbolic.cyclic.contains (decide (stop ≤ start))
          (decide (start ≤ key)) (decide (key < stop))) =
        Aeneas.Std.RustM.ok (inGap start stop key) := by
  by_cases a : start = key <;> by_cases b : stop ≤ start <;> by_cases c : start ≤ key <;>
    by_cases d : key < stop <;> simp [a, b, c, d, inGap, commonware_symbolic.cyclic.contains]

/-- Strict interior of the successor arc, including the wraparound and singleton cases. -/
def Between [LinearOrder K] (start stop key : K) : Prop :=
  if start < stop then start < key ∧ key < stop else start < key ∨ key < stop

/-- The executable interval guard agrees with strict cyclic succession. -/
theorem inGap_iff [LinearOrder K] {start stop key : K} :
    inGap start stop key = true ↔ Between start stop key := by
  unfold inGap Between
  split_ifs <;> simp_all <;> grind

/-- A singleton's arc excludes every key different from its endpoint. -/
theorem singleton_gap [LinearOrder K] (key query : K) :
    inGap key key query = true ↔ key ≠ query := by
  rw [inGap_iff]
  simp [Between]

end
end Qmdb.Ordered
