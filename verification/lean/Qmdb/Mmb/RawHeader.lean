module
import all DY.EquationalTheory.Hash
public import Qmdb.Mmb.Raw

/-! A decoded operation proof opens the current root to its own leaf count and inactive-peak
boundary. A public reader can use these dimensions directly. -/

namespace Qmdb.Mmb
open DY Active
@[expose] public section

private def wide (get : Field → Bytes) (e : Shape) := (e.fill get).value.length = 32

@[simp] private theorem wide_hash (get : Field → Bytes) (e : Shape) : wide get (.hash e) := by
  simp [wide, Shape.fill, Expr.value, Hash.hashLength]

private theorem wide_peak (get : Field → Bytes) (g : Bool) (h start off cursor : Nat) :
    wide get (peakShape g h start off cursor) := by
  cases h <;> simp only [peakShape] <;> first | apply wide_hash | split <;> apply wide_hash

private theorem wide_bagPeaks (get : Field → Bytes) (i n : Nat) (first : Shape)
    (rest : List Shape) (w : wide get first) : wide get (bagPeaks i n first rest) := by
  have folded (xs : List Shape) (a : Shape) (ha : wide get a) : wide get (xs.foldl bag a) := by
    induction xs generalizing a with
    | nil => exact ha
    | cons x xs ih => exact ih _ (wide_hash _ _)
  suffices allK : ∀ k, wide get (foldFrom k first rest) from allK _
  intro k
  unfold foldFrom
  cases (rest.drop k).reverse
  · exact folded _ _ w
  · exact wide_hash _ _

private theorem wide_foldTarget (get : Field → Bytes) (i n : Nat) (left right : List Shape)
    (target : Shape) (hl : ∀ l ∈ left, wide get l) (ht : wide get target) :
    wide get (foldTarget i n left target right) := by
  cases left with
  | nil => exact wide_bagPeaks _ _ _ _ _ ht
  | cons l ls => exact wide_bagPeaks _ _ _ _ _ (hl _ (by simp))

private theorem assemble_bag (p : RawProof) (item : Bytes) (leaves inactive loc i h off n : Nat)
    (g : Bool) (ops : p.opsRoot.length = 32) (widths : ∀ d ∈ p.digests, d.length = 32) :
    ∃ b, (assemble leaves inactive loc i h off n g).tree = envelope leaves inactive loc b ∧
      wide (p.get item) b := by
  unfold assemble
  refine ⟨_, rfl, wide_foldTarget _ _ _ _ _ _ ?_ (wide_peak _ _ _ _ _ _)⟩
  intro l hl
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hl
  simp only [wide, Shape.fill, Expr.value, RawProof.get]
  cases hd : p.digests[j]? with
  | none => exact ops
  | some d => exact widths d (List.mem_of_getElem? hd)

private theorem suffix_width {present covered : Bool} {s : Option Bytes} {chunk ops : Bytes}
    (width : ops.length = 32) (ok : suffixMatches present covered s chunk = true) :
    (s.getD ops).length = 32 := by
  cases s <;> cases present <;> simp_all [suffixMatches]

private theorem heights_length (u k : Nat) : (peakHeights u k).length = k := by
  induction k <;> simp_all [peakHeights]

/-- Reconstruct a header witness from the decoded proof alone. -/
theorem RawProof.header_of_verify {p : RawProof} {root : Bytes} {leaves inactive loc : Nat}
    {item : Bytes} (accepted : p.verify root leaves inactive loc item = true) :
    ∃ h : Header, h.root = root ∧ h.leaves.toNat = leaves ∧ h.inactive.toNat = inactive := by
  by_cases inside : loc < leaves
  case neg => simp [verify, reconstruct, plan, inside] at accepted
  by_cases limit : leaves ≤ 0x400000000000001e
  case neg => simp [verify, reconstruct, plan, limit] at accepted
  by_cases bound : inactive ≤ (heights leaves).length
  case neg => simp [verify, reconstruct, plan, inside, limit, bound] at accepted
  cases hc : containing (heights leaves) 0 loc with
  | none => simp [verify, reconstruct, plan, inside, limit, bound, hc] at accepted
  | some info =>
    obtain ⟨i, height, off⟩ := info
    let recipe := assemble leaves inactive loc i height off (heights leaves).length
      (loc / 256 < graftedChunks leaves)
    have sel : plan leaves inactive loc true = some recipe := by
      simp [plan, inside, limit, bound, hc, recipe]
    by_cases valid : p.fieldsValid recipe leaves loc = true
    case neg => simp [verify, reconstruct, sel, valid] at accepted
    have calcRoot : (recipe.tree.fill (p.get item)).value = root := by
      simpa [verify, reconstruct, sel, valid] using accepted
    simp only [fieldsValid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at valid
    obtain ⟨⟨⟨⟨⟨⟨_, _⟩, ops⟩, widths⟩, _⟩, pendOK⟩, trailOK⟩ := valid
    obtain ⟨b, env, bagWide⟩ := assemble_bag p item leaves inactive loc i height off _ _ ops widths
    change (recipe.tree.fill _).value = root at calcRoot
    rw [show recipe.tree = _ from env] at calcRoot
    let complete := leaves / 256
    let resolved := graftedChunks leaves
    let takeChunk (covered : Bool) (s : Option Bytes) (hw : (s.getD p.opsRoot).length = 32) :
        Digest :=
      if covered then ⟨Hash.hash (literal p.chunk), by simp [Hash.hashLength]⟩
      else ⟨s.getD p.opsRoot, hw⟩
    let pending := takeChunk (loc / 256 = resolved) p.pending (suffix_width ops pendOK)
    let trailing := takeChunk (loc / 256 = complete) p.trailing (suffix_width ops trailOK)
    have leafWidth : leaves < UInt64.size := by change leaves < 2^64; omega
    have splitWidth : inactive < UInt64.size := by
      simp [heights, heights_length] at bound
      have := Nat.log2_le_self (leaves + 1)
      change inactive < 2^64
      omega
    have leafNat := UInt64.toNat_ofNat_of_lt' leafWidth
    have splitNat := UInt64.toNat_ofNat_of_lt' splitWidth
    have leafNZ : UInt64.ofNat leaves ≠ 0 := by
      intro zero
      apply_fun UInt64.toNat at zero
      simp [leafNat] at zero
      omega
    have inactiveZero : UInt64.ofNat inactive = 0 ↔ inactive = 0 := by
      constructor
      · intro zero
        apply_fun UInt64.toNat at zero
        simpa [splitNat] using zero
      · rintro rfl; rfl
    let hdr : Header :=
      ⟨UInt64.ofNat leaves, UInt64.ofNat inactive, (fun h => (leafNZ h).elim),
       ⟨_, bagWide⟩, ⟨_, ops⟩, if resolved < complete then some pending else none,
       if leaves % 256 ≠ 0 then some (UInt64.ofNat (leaves % 256), trailing) else none⟩
    refine ⟨hdr, ?_, leafNat, splitNat⟩
    rw [← calcRoot]
    dsimp only [hdr, Header.root]
    unfold envelope merkleShape
    dsimp only
    by_cases pe : resolved < complete <;> by_cases tr : leaves % 256 = 0 <;>
      by_cases ip : inactive = 0 <;> by_cases cp : loc / 256 = resolved <;>
      by_cases ct : loc / 256 = complete <;>
      dsimp [complete, resolved] at pe cp ct ⊢ <;>
      simp [CurrentRoot.term, Header.input, Header.dimensions, leafNZ, inactiveZero, Shape.fill,
        Expr.value, RawProof.get, pending, trailing, takeChunk, complete, resolved, pe, tr, ip, cp,
        ct] <;>
      split_ifs <;> rfl

end
end Qmdb.Mmb
