module
public import Commonware.Symbolic.Signing

/-! The extracted production certificate rules and the client under an arbitrary signature scheme.
The rules return a verdict on every input and accept exactly when the signer flags span the
committee, name at least its quorum, and the signature decodes and signs the subject under the
sum of the keys of the named members. From that: what a signer index means, that a quorum of
distinct members is named, which subject is signed, and that two quorums of one committee share
more members than it tolerates as faulty. Checked by Lean; only the statements matter for
review. -/

namespace Bls.Certificate
open Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

variable {K P : Type}

/-! ## Signer flags -/

theorem selected_nil_left (keys : List K) : selected [] keys = [] := by
  cases keys <;> rfl

theorem selected_nil_right (bits : List Bool) : selected bits ([] : List K) = [] := by
  cases bits with
  | nil => rfl
  | cons bit bits => cases bit <;> rfl

/-- Every index that the flags name is at least `first`. -/
theorem le_of_mem_namedFrom {index : Nat} : ∀ (bits : List Bool) (first : Nat),
    index ∈ namedFrom first bits → first ≤ index
  | [], _, mem => by simp [namedFrom] at mem
  | true :: bits, first, mem => by
    simp only [namedFrom, List.mem_cons] at mem
    rcases mem with rfl | later
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (le_of_mem_namedFrom bits (first + 1) later)
  | false :: bits, first, mem =>
    Nat.le_of_succ_le (le_of_mem_namedFrom bits (first + 1) (by simpa [namedFrom] using mem))

/-- The flags name exactly the indices whose flag is set. -/
theorem mem_namedFrom {index : Nat} : ∀ (bits : List Bool) (first : Nat),
    index ∈ namedFrom first bits ↔ first ≤ index ∧ bits[index - first]? = some true
  | [], first => by simp [namedFrom]
  | bit :: bits, first => by
    have later := mem_namedFrom (index := index) bits (first + 1)
    by_cases here : index = first
    · subst here
      have absent : index ∉ namedFrom (index + 1) bits := fun mem =>
        Nat.lt_irrefl _ (le_of_mem_namedFrom bits _ mem)
      cases bit <;> simp [namedFrom, absent]
    · have shift : first ≤ index → index - first = (index - (first + 1)) + 1 := by omega
      cases bit
      · simp only [namedFrom, later]
        constructor
        · rintro ⟨above, flag⟩
          exact ⟨by omega, by rw [shift (by omega)]; simpa using flag⟩
        · rintro ⟨above, flag⟩
          refine ⟨by omega, ?_⟩
          rw [shift above] at flag
          simpa using flag
      · simp only [namedFrom, List.mem_cons, here, false_or, later]
        constructor
        · rintro ⟨above, flag⟩
          exact ⟨by omega, by rw [shift (by omega)]; simpa using flag⟩
        · rintro ⟨above, flag⟩
          refine ⟨by omega, ?_⟩
          rw [shift above] at flag
          simpa using flag

/-- The named indices ascend, so no index is named twice. -/
theorem namedFrom_sorted : ∀ (bits : List Bool) (first : Nat),
    (namedFrom first bits).Pairwise (· < ·)
  | [], _ => by simp [namedFrom]
  | true :: bits, first => by
    simp only [namedFrom, List.pairwise_cons]
    exact ⟨fun index mem => le_of_mem_namedFrom bits _ mem, namedFrom_sorted bits _⟩
  | false :: bits, first => by
    simpa [namedFrom] using namedFrom_sorted bits (first + 1)

/-- As many indices are named as flags are set. -/
theorem length_namedFrom : ∀ (bits : List Bool) (first : Nat),
    (namedFrom first bits).length = bits.count true
  | [], _ => by simp [namedFrom]
  | true :: bits, first => by simp [namedFrom, length_namedFrom bits]
  | false :: bits, first => by simp [namedFrom, length_namedFrom bits]

/-- The selected keys are the keys of the named indices, in index order. -/
theorem selected_eq : ∀ (bits : List Bool) (keys : List K) (first : Nat),
    selected bits keys = (namedFrom first bits).filterMap fun index => keys[index - first]?
  | [], keys, _ => by simp [selected_nil_left, namedFrom]
  | bit :: bits, [], _ => by simp [selected_nil_right]
  | bit :: bits, key :: keys, first => by
    have shifted : (namedFrom (first + 1) bits).filterMap (fun index => (key :: keys)[index - first]?) =
        (namedFrom (first + 1) bits).filterMap fun index => keys[index - (first + 1)]? := by
      apply List.filterMap_congr
      intro index mem
      have above := le_of_mem_namedFrom bits _ mem
      have : index - first = (index - (first + 1)) + 1 := by omega
      rw [this]
      simp
    cases bit
    · simp only [selected, namedFrom, shifted]
      exact selected_eq bits keys (first + 1)
    · simp only [selected, namedFrom, List.filterMap_cons, Nat.sub_self, List.getElem?_cons_zero,
        shifted]
      rw [selected_eq bits keys (first + 1)]

/-! ## Counting the signers -/

/-- The counting loop adds the flags that are set from `index` on. -/
theorem count_loop_eq (f : Flags) (rest : Nat) : ∀ (count index : Std.U64),
    index.val + rest = f.bits.length → count.val ≤ index.val →
    ∃ result, rules.count_loop Flags.signers f f.bound count index = RustM.ok result ∧
      result.val = count.val + (f.bits.drop index.val).count true := by
  induction rest with
  | zero =>
    intro count index at_end _
    refine ⟨count, ?_, ?_⟩
    · unfold rules.count_loop
      apply loop_done
      have done : ¬ index < f.bound := by
        simp [Flags.bound_val]; omega
      simp [rules.count_loop.body, done]
    · have : f.bits.drop index.val = [] := List.drop_eq_nil_of_le (by omega)
      simp [this]
  | succ rest ih =>
    intro count index more small
    have bounded := f.bounded
    have inside : index.val < f.bits.length := by omega
    have more' : index < f.bound := by simp [Flags.bound_val]; omega
    obtain ⟨next, hnext, nextv⟩ := add_ok index 1#u64 (by scalar_tac)
    obtain ⟨bit, flag⟩ : ∃ bit, f.bits[index.val]? = some bit :=
      ⟨_, List.getElem?_eq_getElem inside⟩
    have split : f.bits.drop index.val = bit :: f.bits.drop (index.val + 1) := by
      rw [List.drop_eq_getElem_cons inside, (List.getElem?_eq_some_iff.mp flag).2]
    cases bit with
    | false =>
      obtain ⟨result, run, value⟩ :=
        ih count next (by simp [nextv]; omega) (by simp [nextv]; omega)
      refine ⟨result, ?_, ?_⟩
      · unfold rules.count_loop at run ⊢
        rw [loop_cont _ _ (count, next) ?_]
        · exact run
        · simp [rules.count_loop.body, more', Flags.signers, flag, hnext]
      · simp [value, split, nextv]
    | true =>
      obtain ⟨more_count, hcount, countv⟩ := add_ok count 1#u64 (by scalar_tac)
      obtain ⟨result, run, value⟩ := ih more_count next (by simp [nextv]; omega)
        (by simp [nextv, countv]; omega)
      refine ⟨result, ?_, ?_⟩
      · unfold rules.count_loop at run ⊢
        rw [loop_cont _ _ (more_count, next) ?_]
        · exact run
        · simp [rules.count_loop.body, more', Flags.signers, flag, hnext, hcount]
      · simp [value, split, nextv, countv]; omega

/-- The rules count the flags that are set. -/
theorem count_eq (f : Flags) :
    ∃ count, rules.count Flags.signers f = RustM.ok count ∧ count.val = f.bits.count true := by
  obtain ⟨count, run, value⟩ := count_loop_eq f f.bits.length 0#u64 0#u64 (by simp) (by simp)
  refine ⟨count, ?_, by simpa using value⟩
  simpa [rules.count, Flags.signers] using run

/-! ## Combining the keys -/

/-- The combining loop adds the keys of the members that the flags name from `index` on. -/
theorem aggregate_loop_eq (S : Signing K P) {C : Type} (inst : rules.Committee C K) (committee : C)
    (keys : List K) (quorum : Std.U64) (reads : Reads inst committee keys quorum) (f : Flags)
    (covered : f.bits.length ≤ keys.length) (rest : Nat) : ∀ (sum : K) (index : Std.U64),
    index.val + rest = f.bits.length →
    rules.aggregate_loop S.terms inst Flags.signers () committee f f.bound sum index =
      RustM.ok (some (S.extend sum (selected (f.bits.drop index.val) (keys.drop index.val)))) := by
  induction rest with
  | zero =>
    intro sum index at_end
    unfold rules.aggregate_loop
    have done : ¬ index < f.bound := by
      simp [Flags.bound_val]; omega
    have empty : f.bits.drop index.val = [] := List.drop_eq_nil_of_le (by omega)
    rw [loop_done _ _ (some sum) (by simp [rules.aggregate_loop.body, done])]
    simp [empty, selected_nil_left, Signing.extend]
  | succ rest ih =>
    intro sum index more
    have bounded := f.bounded
    have inside : index.val < f.bits.length := by omega
    have member : index.val < keys.length := by omega
    have more' : index < f.bound := by simp [Flags.bound_val]; omega
    obtain ⟨next, hnext, nextv⟩ := add_ok index 1#u64 (by scalar_tac)
    obtain ⟨bit, flag⟩ : ∃ bit, f.bits[index.val]? = some bit :=
      ⟨_, List.getElem?_eq_getElem inside⟩
    have split : f.bits.drop index.val = bit :: f.bits.drop (index.val + 1) := by
      rw [List.drop_eq_getElem_cons inside, (List.getElem?_eq_some_iff.mp flag).2]
    have keyed : keys.drop index.val = keys[index.val] :: keys.drop (index.val + 1) :=
      List.drop_eq_getElem_cons member
    have nextn : next.val = index.val + 1 := by simp [nextv]
    cases bit with
    | false =>
      have run := ih sum next (by omega)
      unfold rules.aggregate_loop at run ⊢
      rw [loop_cont _ _ (sum, next) (by
        simp [rules.aggregate_loop.body, more', Flags.signers, flag, hnext])]
      rw [run, split, keyed, nextn]
      simp [selected]
    | true =>
      have run := ih (S.add sum keys[index.val]) next (by omega)
      unfold rules.aggregate_loop at run ⊢
      rw [loop_cont _ _ (S.add sum keys[index.val], next) (by
        simp [rules.aggregate_loop.body, more', Flags.signers, flag, hnext, reads.key,
          List.getElem?_eq_getElem member, Signing.terms])]
      rw [run, split, keyed, nextn]
      simp [selected, Signing.extend]

/-- The rules combine the keys of the members that the flags name, in index order. -/
theorem aggregate_eq (S : Signing K P) {C : Type} (inst : rules.Committee C K) (committee : C)
    (keys : List K) (quorum : Std.U64) (reads : Reads inst committee keys quorum) (f : Flags)
    (covered : f.bits.length ≤ keys.length) :
    rules.aggregate S.terms inst Flags.signers () committee f =
      RustM.ok (some (S.sum (selected f.bits keys))) := by
  have run := aggregate_loop_eq S inst committee keys quorum reads f covered f.bits.length S.zero
    0#u64 (by simp)
  simpa [rules.aggregate, Flags.signers, Signing.terms, Signing.sum] using run

/-! ## The certificate rules -/

/-- What the rules check of a certificate: its flags span the committee, name at least `quorum`
members, and its signature decodes and signs the subject under the sum of the named keys. -/
def Checks (S : Signing K P) (keys : List K) (quorum : Nat) (bits : List Bool)
    (signature : Option P) (ns message : Slice Std.U8) : Prop :=
  bits.length = keys.length ∧ quorum ≤ bits.count true ∧
    ∃ point, signature = some point ∧
      S.check (S.sum (selected bits keys)) (S.hash ns message) point = true

/-- The certificate rules return a verdict on every input, and accept exactly what `Checks`
describes. -/
theorem verify_certificate_iff (S : Signing K P) {C : Type} (inst : rules.Committee C K)
    (committee : C) (keys : List K) (quorum : Std.U64) (reads : Reads inst committee keys quorum)
    (f : Flags) (signature : Option P) (ns message : Slice Std.U8) :
    ∃ verdict, rules.verify_certificate S.terms inst Flags.signers decoded () committee f
        signature ns message = RustM.ok verdict ∧
      (verdict = true ↔ Checks S keys quorum.val f.bits signature ns message) := by
  obtain ⟨members, hmembers, membersv⟩ := reads.members
  obtain ⟨count, hcount, countv⟩ := count_eq f
  have hbound : Flags.signers.bound f = RustM.ok f.bound := rfl
  have hdecoded : (decoded (P := P)).decoded signature = RustM.ok signature := rfl
  unfold rules.verify_certificate
  by_cases spans : f.bits.length = keys.length
  · have same : f.bound = members :=
      UScalar.eq_of_val_eq (by rw [Flags.bound_val, membersv, spans])
    by_cases enough : quorum.val ≤ f.bits.count true
    · have reached : ¬ count.val < quorum.val := by omega
      cases signature with
      | none =>
        refine ⟨false, ?_, by simp [Checks]⟩
        simp [hbound, hmembers, same, hcount, reads.quorum, hdecoded]
      | some point =>
        have hmessage : S.terms.message () ns message = RustM.ok (S.hash ns message) := rfl
        have hcheck (key : K) (hashed : P) :
            S.terms.check () key hashed point = RustM.ok (S.check key hashed point) := rfl
        refine ⟨S.check (S.sum (selected f.bits keys)) (S.hash ns message) point, ?_,
          by simp [Checks, spans, enough]⟩
        simp [hbound, hmembers, same, hcount, reads.quorum, reached, hdecoded,
          aggregate_eq S inst committee keys quorum reads f (by omega), hmessage, hcheck]
    · have short : count.val < quorum.val := by omega
      refine ⟨false, ?_, by simp [Checks, enough]⟩
      simp [hbound, hmembers, same, hcount, reads.quorum, short]
  · have differ : ¬ f.bound.val = members.val := by
      rw [Flags.bound_val, membersv]
      exact spans
    refine ⟨false, ?_, by simp [Checks, spans]⟩
    simp [hbound, hmembers, differ]

/-- The attestation rule returns a verdict on every input, and accepts exactly a signature that
decodes and signs the subject under the key of the member at the signer index. -/
theorem verify_attestation_iff (S : Signing K P) {C : Type} (inst : rules.Committee C K)
    (committee : C) (keys : List K) (quorum : Std.U64) (reads : Reads inst committee keys quorum)
    (signer : Std.U64) (signature : Option P) (ns message : Slice Std.U8) :
    ∃ verdict, rules.verify_attestation S.terms inst decoded () committee signer signature ns
        message = RustM.ok verdict ∧
      (verdict = true ↔ ∃ key point, keys[signer.val]? = some key ∧ signature = some point ∧
        S.check key (S.hash ns message) point = true) := by
  have hdecoded : (decoded (P := P)).decoded signature = RustM.ok signature := rfl
  have hmessage : S.terms.message () ns message = RustM.ok (S.hash ns message) := rfl
  unfold rules.verify_attestation
  cases member : keys[signer.val]? with
  | none => exact ⟨false, by simp [reads.key, member], by simp⟩
  | some key =>
    cases signature with
    | none => exact ⟨false, by simp [reads.key, member, hdecoded], by simp⟩
    | some point =>
      have hcheck : S.terms.check () key (S.hash ns message) point =
          RustM.ok (S.check key (S.hash ns message) point) := rfl
      exact ⟨S.check key (S.hash ns message) point,
        by simp [reads.key, member, hdecoded, hmessage, hcheck], by simp⟩

/-- The single-key rule returns a verdict on every input, and accepts exactly a signature that
decodes and signs the subject under that key. -/
theorem verify_identity_iff (S : Signing K P) (identity : K) (signature : Option P)
    (ns message : Slice Std.U8) :
    ∃ verdict, rules.verify_identity S.terms decoded () identity signature ns message =
        RustM.ok verdict ∧
      (verdict = true ↔ ∃ point, signature = some point ∧
        S.check identity (S.hash ns message) point = true) := by
  have hdecoded : (decoded (P := P)).decoded signature = RustM.ok signature := rfl
  have hmessage : S.terms.message () ns message = RustM.ok (S.hash ns message) := rfl
  unfold rules.verify_identity
  cases signature with
  | none => exact ⟨false, by simp [hdecoded], by simp⟩
  | some point =>
    have hcheck : S.terms.check () identity (S.hash ns message) point =
        RustM.ok (S.check identity (S.hash ns message) point) := rfl
    exact ⟨S.check identity (S.hash ns message) point, by simp [hdecoded, hmessage, hcheck],
      by simp⟩

/-! ## The client -/

/-- The `N3f1` quorum of a committee of `members`: all but the faults it tolerates. -/
def quorum (members : Nat) : Nat :=
  members - (members - 1) / 3

/-- With the client's fault model, a committee that is not empty asks for its `N3f1` quorum. -/
theorem n3f1_reads {C : Type} (inst : rules.Committee C K) (committee : C) (keys : List K)
    (asked : Std.U64) (reads : Reads inst committee keys asked) (members : keys ≠ []) :
    ∃ needed : Std.U64, needed.val = quorum keys.length ∧
      Reads (bls.N3f1.Insts.Commonware_symbolicRulesCommittee inst) committee keys needed := by
  obtain ⟨count, hcount, countv⟩ := reads.members
  have positive : 0 < keys.length := List.length_pos_iff.mpr members
  obtain ⟨less, hless, lessv⟩ := sub_ok count 1#u64 (by scalar_tac)
  obtain ⟨faults, hfaults, faultsv⟩ := UScalar.div_spec less (y := 3#u64) (by decide)
  have faultsn : faults.val = (keys.length - 1) / 3 := by
    simp at faultsv lessv; omega
  obtain ⟨needed, hneeded, neededv⟩ := sub_ok count faults (by omega)
  refine ⟨needed, by simp [quorum, neededv, countv, faultsn], ⟨count, ?_, countv⟩, ?_, ?_⟩
  · simpa [bls.N3f1.Insts.Commonware_symbolicRulesCommittee.members] using hcount
  · simp [bls.N3f1.Insts.Commonware_symbolicRulesCommittee.quorum, hcount, hless, hfaults,
      hneeded]
  · intro index
    simpa [bls.N3f1.Insts.Commonware_symbolicRulesCommittee.key] using reads.key index

/-- What the client checks before it accepts a certificate of the committee with `keys`. -/
def Accepts (S : Signing K P) (keys : List K) (bits : List Bool) (signature : Option P)
    (ns message : Slice Std.U8) : Prop :=
  keys ≠ [] ∧ Checks S keys (quorum keys.length) bits signature ns message

/-- The client step returns on every input. It accepts exactly what `Accepts` describes, and the
event it returns names the committee size and its quorum. -/
theorem client_step_iff (S : Signing K P) {C : Type} (inst : rules.Committee C K) (committee : C)
    (keys : List K) (asked : Std.U64) (reads : Reads inst committee keys asked) (f : Flags)
    (signature : Option P) (ns message : Slice Std.U8) :
    ∃ event, bls.client_step S.terms inst Flags.signers decoded () committee ns message f
        signature = RustM.ok event ∧
      (event.isSome ↔ Accepts S keys f.bits signature ns message) ∧
      ∀ certified, event = some certified →
        certified.members.val = keys.length ∧ certified.quorum.val = quorum keys.length := by
  obtain ⟨count, hcount, countv⟩ := reads.members
  unfold bls.client_step
  by_cases members : keys = []
  · have zero : count = 0#u64 := UScalar.eq_of_val_eq (by simp [countv, members])
    refine ⟨none, ?_, by simp [Accepts, members], by simp⟩
    simp [bls.N3f1.Insts.Commonware_symbolicRulesCommittee.members, hcount, zero]
  · have positive : 0 < keys.length := List.length_pos_iff.mpr members
    have nonzero : ¬ count.val = 0 := by omega
    obtain ⟨needed, neededv, wrapped⟩ := n3f1_reads inst committee keys asked reads members
    obtain ⟨verdict, run, accepts⟩ := verify_certificate_iff S _ committee keys needed wrapped f
      signature ns message
    rw [neededv] at accepts
    cases verdict with
    | false =>
      refine ⟨none, ?_, by simpa [Accepts, members] using accepts, by simp⟩
      simp [bls.N3f1.Insts.Commonware_symbolicRulesCommittee.members, hcount, run]
    | true =>
      refine ⟨some { members := count, quorum := needed }, ?_,
        by simpa [Accepts, members] using accepts, ?_⟩
      · have hneeded : bls.N3f1.Insts.Commonware_symbolicRulesCommittee.quorum inst committee =
            RustM.ok needed := wrapped.quorum
        simp [bls.N3f1.Insts.Commonware_symbolicRulesCommittee.members, hcount, nonzero, run,
          hneeded]
      · intro certified same
        cases same
        exact ⟨countv, neededv⟩

/-! ## What acceptance means -/

/-- Signer-index interpretation: an accepted certificate has one flag per committee member, and
its signature is checked under the keys of exactly the members whose flags are set, each taken
once, in index order. -/
theorem signer_index_interpretation {S : Signing K P} {keys : List K} {bits : List Bool}
    {signature : Option P} {ns message : Slice Std.U8}
    (accepted : Accepts S keys bits signature ns message) :
    bits.length = keys.length ∧
      selected bits keys = (named bits).filterMap (fun index => keys[index]?) ∧
      (named bits).Pairwise (· < ·) ∧
      ∀ index, index ∈ named bits ↔ bits[index]? = some true := by
  refine ⟨accepted.2.1, by simpa using selected_eq bits keys 0, namedFrom_sorted bits 0, ?_⟩
  intro index
  simpa using mem_namedFrom (index := index) bits 0

/-- Quorum authorization: an accepted certificate names at least the `N3f1` quorum of the
committee, all of them members and no member twice. -/
theorem quorum_authorization {S : Signing K P} {keys : List K} {bits : List Bool}
    {signature : Option P} {ns message : Slice Std.U8}
    (accepted : Accepts S keys bits signature ns message) :
    quorum keys.length ≤ (named bits).length ∧ (named bits).Nodup ∧
      ∀ index ∈ named bits, index < keys.length := by
  refine ⟨by rw [length_namedFrom]; exact accepted.2.2.1,
    (namedFrom_sorted bits 0).imp (fun order => Nat.ne_of_lt order), ?_⟩
  intro index mem
  have flag := (mem_namedFrom bits 0).mp mem
  have inside : index < bits.length := by
    have := List.getElem?_eq_some_iff.mp flag.2
    obtain ⟨bound, -⟩ := this
    simpa using bound
  rw [← accepted.2.1]
  exact inside

/-- Subject binding: the signature of an accepted certificate signs the hash of exactly the
namespace and message that the client was asked about, under the sum of the named keys. -/
theorem subject_binding {S : Signing K P} {keys : List K} {bits : List Bool}
    {signature : Option P} {ns message : Slice Std.U8}
    (accepted : Accepts S keys bits signature ns message) :
    ∃ point, signature = some point ∧
      S.check (S.sum (selected bits keys)) (S.hash ns message) point = true :=
  accepted.2.2.2

/-! ## Quorum intersection -/

/-- Flags set in both lists number at least the two counts less the length. -/
theorem count_both : ∀ (a b : List Bool), a.length = b.length →
    a.count true + b.count true ≤ (List.zipWith (· && ·) a b).count true + a.length
  | [], [], _ => by simp
  | x :: a, y :: b, same => by
    have rest := count_both a b (by simpa using same)
    cases x <;> cases y <;> simp <;> omega
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same

/-- The indices that both lists of flags name. -/
def common (a b : List Bool) : List Nat :=
  named (List.zipWith (· && ·) a b)

theorem mem_common {a b : List Bool} {index : Nat} :
    index ∈ common a b ↔ index ∈ named a ∧ index ∈ named b := by
  simp only [common, named, mem_namedFrom, Nat.zero_le, true_and, Nat.sub_zero,
    List.getElem?_zipWith]
  cases a[index]? <;> cases b[index]? <;> simp

/-- Quorum intersection: two lists of flags over one committee that each name its `N3f1` quorum
name more common members than the committee tolerates as faulty. -/
theorem quorum_intersection (members : Nat) (a b : List Bool) (positive : 0 < members)
    (la : a.length = members) (lb : b.length = members) (qa : quorum members ≤ a.count true)
    (qb : quorum members ≤ b.count true) : (members - 1) / 3 < (common a b).length := by
  have both := count_both a b (by rw [la, lb])
  rw [common, length_namedFrom]
  unfold quorum at qa qb
  omega

end
end Bls.Certificate
