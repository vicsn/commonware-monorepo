module
public import Bls.Protocol
meta import Bls.Certificate
meta import Commonware.Symbolic.Signing

/-! A committee of four members with their own keys, and the extracted client's decisions on it:
a quorum's certificate is accepted; too few signers, flags of the wrong length and another
subject are rejected, whatever the signature. Then two attack models from One For All. A rogue
key, registered without a proof of possession, gets a certificate accepted that names a member
who never signed. Two keys whose secrets sum to zero make one signature verify under two
different sets of signers. The decisions are proved; the flag arithmetic is also executed. -/

namespace Bls.Sanity
open DY Aeneas Aeneas.Std Commonware.Symbolic Commonware.Symbolic.Linear Certificate Protocol
open commonware_symbolic
@[expose] public section

/-- The namespace of the subjects. -/
def ns : Slice Std.U8 := Slice.from [78#u8] (by scalar_tac)

/-- A subject. -/
def subject : Slice Std.U8 := Slice.from [1#u8] (by scalar_tac)

/-- Another subject. -/
def other : Slice Std.U8 := Slice.from [2#u8, 2#u8] (by scalar_tac)

theorem subject_ne_other : subject ≠ other := by
  intro same
  have := congrArg (fun s : Slice Std.U8 => s.val.length) same
  simp [subject, other, Slice.from_val] at this

/-- Signer flags, one per member. -/
def flags (bits : List Bool) (small : bits.length < 2 ^ 64 := by decide) : Flags :=
  ⟨bits, small⟩

/-- A committee of four members that registered their own keys, under a hash that keeps inputs
apart. -/
instance committee : Setup where
  Hashed := Input (Slice Std.U8)
  hash := id
  keys := [basis 0, basis 1, basis 2, basis 3]
  bounded := by decide

noncomputable section

/-- The signature of members 0, 1 and 2 over `message`. -/
def signature (message : Slice Std.U8) : Sig (Input (Slice Std.U8)) :=
  term (total [basis 0, basis 1, basis 2]) (.message ns message)

/-- The client's decision on a certificate for `message`. -/
abbrev verdict (signers : Flags) (message : Slice Std.U8) (sig : Sig (Input (Slice Std.U8))) :=
  decision ⟨ns, message, signers, sig⟩

/-- The client's decision is what the extracted step accepts. -/
theorem verdict_none {signers : Flags} {message : Slice Std.U8}
    {sig : Sig (Input (Slice Std.U8))}
    (rejected : ¬ Accepts (scheme id) [basis 0, basis 1, basis 2, basis 3] signers.bits
      (some (Point.signature sig)) ns message) :
    verdict signers message sig = RustM.ok none := by
  obtain ⟨found, ran, accepts, -⟩ := client_step_iff (scheme Setup.hash)
    Roster.committee roster Setup.keys 0#u64 (roster.reads) signers
    (some (Point.signature sig)) ns message
  cases found with
  | none => simp [decision, ran]
  | some certified => exact absurd (accepts.mp rfl) rejected

/-- The certificate of members 0, 1 and 2 for the subject is accepted, and the logged event names
the committee of four and its quorum of three. -/
theorem accepts_quorum : verdict (flags [true, true, true, false]) subject (signature subject) =
    RustM.ok (some (Event.certify ns subject [true, true, true, false]
      { members := 4#u64, quorum := 3#u64 })) := by
  obtain ⟨found, ran, accepts, names⟩ := client_step_iff (scheme Setup.hash)
    Roster.committee roster Setup.keys 0#u64 (roster.reads) (flags [true, true, true, false])
    (some (Point.signature (signature subject))) ns subject
  have accepted : found.isSome := accepts.mpr ⟨by simp [Setup.keys], rfl, by decide, _, rfl, by
    rw [check_iff, sum_eq]
    rfl⟩
  obtain ⟨certified, rfl⟩ := Option.isSome_iff_exists.mp accepted
  obtain ⟨members, needed⟩ := names certified rfl
  have same : certified = { members := 4#u64, quorum := 3#u64 } := by
    cases certified
    simp only [bls.Certified.mk.injEq]
    exact ⟨UScalar.eq_of_val_eq members, UScalar.eq_of_val_eq needed⟩
  simp only [decision, ran]
  simp [same, flags]

/-- Two signers are below the quorum of three, whatever the signature. -/
theorem rejects_below_quorum (sig : Sig (Input (Slice Std.U8))) :
    verdict (flags [true, true, false, false]) subject sig = RustM.ok none :=
  verdict_none fun accepted => absurd accepted.2.2.1 (by decide)

/-- Flags for five members do not span the committee of four, whatever the signature. -/
theorem rejects_wrong_length (sig : Sig (Input (Slice Std.U8))) :
    verdict (flags [true, true, true, false, false]) subject sig = RustM.ok none :=
  verdict_none fun accepted => absurd accepted.2.1 (by decide)

/-- The signature over the subject does not certify another subject. -/
theorem rejects_other_subject :
    verdict (flags [true, true, true, false]) other (signature subject) = RustM.ok none := by
  apply verdict_none
  rintro ⟨-, -, -, point, decodes, checks⟩
  cases decodes
  have same := (Point.signature.injEq _ _).mp ((check_iff id _ ns other _).mp checks)
  rw [sum_eq] at same
  have at_subject := congrFun (congrFun same (.message ns subject)) 0
  have apart : (Input.message ns subject : Input (Slice Std.U8)) ≠ Input.message ns other :=
    fun eq => subject_ne_other (Input.message.inj eq).2
  simp [signature, term, total, basis, apart] at at_subject

/-! ## A rogue key -/

/-- Nobody signed anything. -/
def nobody : Nat → Slice Std.U8 → Slice Std.U8 → Prop := fun _ _ _ => False

/-- Only member 1 is compromised. -/
def second : Nat → Prop := fun member => member = 1

/-- A key that cancels member 0's secret: the secret of member 1 less that of member 0. -/
def rogue : Key := fun member => basis 1 member - basis 0 member

/-- Without proofs of possession a rogue key breaks authentication. Member 0 registered its own
key and member 1 the rogue key. With member 1's secret alone, and no signature from member 0,
the attacker derives a signature that is accepted for both members. The rogue key has no
derivable proof of possession, which is why the trace theorem asks for one. -/
theorem rogue_key_accepted :
    Accepts (scheme (id : Input (Slice Std.U8) → _)) [basis 0, rogue] [true, true]
        (some (Point.signature (term (basis 1) (.message ns subject)))) ns subject ∧
      Derives id nobody second (term (basis 1) (id (Input.message ns subject))) ∧
      ¬ Derives id nobody second
        (term rogue (id (Input.possession (B := Slice Std.U8) rogue))) := by
  refine ⟨⟨by simp, rfl, by decide, _, rfl, ?_⟩,
    Derives.corrupt (hash := id) (signed := nobody) (leaked := second) (member := 1) rfl _, ?_⟩
  · rw [check_iff, sum_eq]
    have sum : total (selected [true, true] [basis 0, rogue]) = basis 1 := by
      funext member
      simp [total, selected, rogue]
    rw [sum]
    rfl
  · intro derived
    obtain ⟨input, same, origin⟩ := support (member := 0) derived (by simp [second])
      (Input.possession rogue) (by simp [term, rogue, basis])
    cases same
    have at_one := congrFun (show rogue = basis 0 from origin) 1
    simp [rogue, basis] at at_one

/-! ## Keys that sum to zero -/

/-- Only member 5 is compromised. -/
def sixth : Nat → Prop := fun member => member = 5

/-- The key whose secret is the opposite of member 5's. -/
def opposite : Key := fun member => - basis 5 member

/-- Five members with their own keys, and two keys whose secrets sum to zero. -/
def split : List Key :=
  [basis 0, basis 1, basis 2, basis 3, basis 4, basis 5, opposite]

/-- The signature of members 0 to 4 over the subject. -/
def five : Sig (Input (Slice Std.U8)) :=
  term (total [basis 0, basis 1, basis 2, basis 3, basis 4]) (.message ns subject)

/-- Keys that sum to zero break signer-set binding. Whoever holds member 5's secret can prove
possession of both keys, so both pass registration. Then the signature of members 0 to 4 is
accepted with their five flags, and also with all seven: the two extra members are named without
contributing anything. -/
theorem splitting_zero :
    Accepts (scheme (id : Input (Slice Std.U8) → _)) split
        [true, true, true, true, true, false, false] (some (Point.signature five)) ns subject ∧
      Accepts (scheme (id : Input (Slice Std.U8) → _)) split
        [true, true, true, true, true, true, true] (some (Point.signature five)) ns subject ∧
      Derives id nobody sixth
        (term opposite (id (Input.possession (B := Slice Std.U8) opposite))) := by
  refine ⟨⟨by simp [split], rfl, by decide, _, rfl, ?_⟩,
    ⟨by simp [split], rfl, by decide, _, rfl, ?_⟩, ?_⟩
  · rw [check_iff, sum_eq]
    rfl
  · rw [check_iff, sum_eq]
    have sum : total (selected [true, true, true, true, true, true, true] split) =
        total [basis 0, basis 1, basis 2, basis 3, basis 4] := by
      funext member
      simp [total, selected, split, opposite]
    rw [sum]
    rfl
  · have scaled := Derives.scale (-1) (Derives.corrupt (hash := id) (signed := nobody)
      (leaked := sixth) (member := 5) rfl (Input.possession (B := Slice Std.U8) opposite))
    have same : (fun point member => -1 * term (basis 5) (Input.possession opposite) point member) =
        term opposite (id (Input.possession (B := Slice Std.U8) opposite)) := by
      funext point member
      by_cases here : point = Input.possession opposite
      · simp [term, here, opposite]
      · simp [term, here]
    rw [same] at scaled
    exact scaled

end

-- Executed: the flags of the accepted certificate name members 0, 1 and 2.
#guard named [true, true, true, false] == [0, 1, 2]

-- Executed: the `N3f1` quorum of committees of 0 to 10 members.
#guard (List.range 11).map quorum == [0, 1, 2, 3, 3, 4, 5, 5, 6, 7, 7]

-- Executed: two quorums of the committee of four share members 1 and 2.
#guard common [true, true, true, false] [false, true, true, true] == [1, 2]

end
end Bls.Sanity
