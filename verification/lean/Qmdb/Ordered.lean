module
public import Qmdb.Active
public import Qmdb.Ordered.Journal

/-! Current ordered proofs for a valid committed journal. Snapshot invariants describe the
writer's bitmap, successor links and commit floor. The verifier checks the prover's fields
against the independently authenticated operation before using these invariants. -/

namespace Qmdb.Ordered
open DY
@[expose] public section

/-- An operation codec which preserves all fields, including the tag and successor key. -/
abbrev Encoding (K V : Type) := Operation K V ↪ Bytes

/-- A well-formed snapshot with live updates and a final commit carrying its floor. -/
structure Snapshot (K V : Type) [LinearOrder K] (enc : Encoding K V) where
  /-- Authenticated operations and status bitmap. -/
  auth : Active.Snapshot
  /-- The journal in append order. Only locations below the leaf count are meaningful. -/
  entry : Nat → Operation K V
  /-- The Merkle leaves contain the encoded journal entries. -/
  encoded : ∀ i, i < auth.leaves → enc (entry i) = auth.item i
  /-- Exactly the last update to an undeleted key has a set activity bit. -/
  activeUpdate : ∀ i k v next, i < auth.leaves → entry i = .update k v next →
    (auth.live i ↔ Latest entry k i auth.leaves)
  /-- No other live update lies strictly between a live key and its successor. -/
  adjacent : ∀ i k v next j q w succ, i < auth.leaves → entry i = .update k v next →
    auth.live i → j < auth.leaves → entry j = .update q w succ → auth.live j →
    ¬ Between k next q
  /-- The active commit closes the snapshot, and active operations respect its floor. -/
  commitBounds : ∀ i m floor, i < auth.leaves → entry i = .commit m floor → auth.live i →
    i + 1 = auth.leaves ∧ ∀ j, j < auth.leaves → auth.live j → floor.toNat ≤ j

/-- The logical map is reconstructed by replay, independently of the verifier and bitmap. -/
def Snapshot.lookup [LinearOrder K] {enc : Encoding K V} (s : Snapshot K V enc) (key : K) :
    Option V := replay s.entry key s.auth.leaves

/-- Payloads supplied to the two production proof verifiers. -/
inductive Proof (K V : Type) (P : Type := Active.Proof) where
  /-- The prover supplies the successor in a membership proof. -/
  | member (loc : Nat) (next : K) (opening : P)
  /-- Exclude with an active update and its authenticated successor. -/
  | gap (loc : Nat) (start : K) (value : V) (stop : K) (opening : P)
  /-- Exclude with an active commit whose floor equals its own location. -/
  | empty (loc : UInt64) (metadata : Option V) (opening : P)

/-- Verification of the claimed optional value; a claim/proof variant mismatch rejects. -/
def VerifyWith [LinearOrder K] (enc : Encoding K V) (openOp : Nat → Bytes → P → Prop)
    (key : K) : Option V → Proof K V P → Prop
  | some value, .member loc next p => openOp loc (enc (.update key value next)) p
  | none, .gap loc start value stop p =>
    inGap start stop key = true ∧ openOp loc (enc (.update start value stop)) p
  | none, .empty loc metadata p => openOp loc.toNat (enc (.commit metadata loc)) p
  | _, _ => False

/-- Ordered verification using the public active-operation verifier. -/
abbrev Verifies [LinearOrder K] (enc : Encoding K V) (layout : Active.Layout) (root : Bytes) :=
  VerifyWith enc (Active.Verifies layout root)

/-- A refinement of operation proofs preserves every ordered verifier branch. -/
theorem verifyWith_mono [LinearOrder K] {enc : Encoding K V} {key : K} {raw : Option V}
    {first : Nat → Bytes → P → Prop} {second : Nat → Bytes → Q → Prop}
    (convert : ∀ loc item p, first loc item p → ∃ q, second loc item q)
    {p : Proof K V P} (verified : VerifyWith enc first key raw p) :
    ∃ q, VerifyWith enc second key raw q := by
  cases raw with
  | some value =>
    cases p with
    | member loc next p =>
      obtain ⟨q, h⟩ := convert _ _ _ verified
      exact ⟨.member loc next q, h⟩
    | gap | empty => exact False.elim verified
  | none =>
    cases p with
    | member => exact False.elim verified
    | gap loc start v stop p =>
      obtain ⟨guard, opened⟩ := verified
      obtain ⟨q, h⟩ := convert _ _ _ opened
      exact ⟨.gap loc start v stop q, guard, h⟩
    | empty loc m p =>
      obtain ⟨q, h⟩ := convert _ _ _ verified
      exact ⟨.empty loc m q, h⟩

/-- Verify with the public layout and root of an authenticated snapshot. -/
abbrev Accepts [LinearOrder K] (enc : Encoding K V) (s : Active.Snapshot) :=
  Verifies enc s.layout s.root

private theorem opened [LinearOrder K] {enc : Encoding K V} {s : Snapshot K V enc}
    {op : Operation K V} {loc : Nat} {p : Active.Proof}
    (h : Active.Accepts s.auth loc (enc op) p) :
    loc < s.auth.leaves ∧ s.auth.live loc ∧ s.entry loc = op := by
  obtain ⟨inside, live, eq⟩ := Active.accepted h
  exact ⟨inside, live, enc.injective ((s.encoded loc inside).trans eq.symm)⟩

/-- Every accepted membership or exclusion claim equals the replayed state at its root. -/
theorem accepted_read [LinearOrder K] {enc : Encoding K V} (s : Snapshot K V enc)
    {key : K} {value : Option V} {p : Proof K V} (h : Accepts enc s.auth key value p) :
    value = s.lookup key := by
  cases value with
  | some v =>
    cases p with
    | member loc next _ =>
      obtain ⟨inside, live, eq⟩ := opened (s := s) h
      exact (replay_of_latest inside (by simp [eq, Operation.write])
        ((s.activeUpdate loc key v next inside eq).mp live)).symm
    | gap | empty => exact False.elim h
  | none =>
    cases state : s.lookup key with
    | none => rfl
    | some v =>
      obtain ⟨j, succ, bound, update, last⟩ := latest_of_replay state
      have live := (s.activeUpdate j key v succ bound update).mpr last
      exfalso
      cases p with
      | member => exact h
      | gap i k w next p =>
        obtain ⟨guard, check⟩ := h
        obtain ⟨inside, bit, eq⟩ := opened (s := s) check
        exact s.adjacent i k w next j key v succ inside eq bit bound update live
          (inGap_iff.mp guard)
      | empty i metadata p =>
        obtain ⟨inside, bit, eq⟩ := opened (s := s) h
        obtain ⟨finalLoc, lower⟩ := s.commitBounds i.toNat metadata i inside eq bit
        have floor := lower j bound live
        have : j = i.toNat := by omega
        subst j
        simp [eq] at update

private theorem honest_operation [LinearOrder K] {enc : Encoding K V} (s : Snapshot K V enc)
    {loc : Nat} {op : Operation K V} (inside : loc < s.auth.leaves)
    (live : s.auth.live loc) (entry : s.entry loc = op) :
    ∃ p, Active.Accepts s.auth loc (enc op) p := by
  rw [← entry, s.encoded loc inside]
  exact Active.honest s.auth inside live

/-- Every present replayed value has an accepted membership proof. -/
theorem honest_member [LinearOrder K] {enc : Encoding K V} (s : Snapshot K V enc)
    {key : K} {value : V} (found : s.lookup key = some value) :
    ∃ p, Accepts enc s.auth key (some value) p := by
  obtain ⟨i, next, inside, eq, last⟩ := latest_of_replay found
  have live := (s.activeUpdate i key value next inside eq).mpr last
  obtain ⟨p, h⟩ := honest_operation s inside live eq
  exact ⟨.member i next p, h⟩

/-- A live successor gap supplies an honest exclusion proof for every key in its interior. -/
theorem honest_gap [LinearOrder K] {enc : Encoding K V} (s : Snapshot K V enc)
    {loc : Nat} {key start stop : K} {value : V} (inside : loc < s.auth.leaves)
    (live : s.auth.live loc) (entry : s.entry loc = .update start value stop)
    (gap : Between start stop key) : ∃ p, Accepts enc s.auth key none p := by
  obtain ⟨p, h⟩ := honest_operation s inside live entry
  exact ⟨.gap loc start value stop p, inGap_iff.mpr gap, h⟩

/-- An empty snapshot's final commit supplies an honest exclusion proof for every key. -/
theorem honest_empty [LinearOrder K] {enc : Encoding K V} (s : Snapshot K V enc)
    {loc : UInt64} {m : Option V} (inside : loc.toNat < s.auth.leaves)
    (live : s.auth.live loc.toNat)
    (entry : s.entry loc.toNat = .commit m loc) (key : K) :
    ∃ p, Accepts enc s.auth key none p := by
  obtain ⟨p, h⟩ := honest_operation s inside live entry
  exact ⟨.empty loc m p, h⟩

end
end Qmdb.Ordered
