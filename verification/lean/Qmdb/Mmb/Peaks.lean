module
public import Qmdb.Mmb.Coverage
public import Qmdb.Mmb.PinnedPeaks
public import Commonware.Symbolic.RustM

/-! Correctness of every step of the pinned MMB peak iterator on a valid leaf count.
The fork converts the node count to a valid leaf count before initializing its cursor. -/

namespace Qmdb.Mmb.Peaks
open Aeneas Aeneas.Std Aeneas.Std.WP CoreModels Commonware.Symbolic pinned_peaks
@[expose] public section

/-- Last valid leaf count at Tempo's Commonware revision. -/
abbrev maxLeaves := 0x400000000000001e

/-- A valid successor fits in 63 bits. -/
theorem logBound {n : Nat} (hn : n ≤ maxLeaves + 1) : n.log2 ≤ 62 := by
  by_cases z : n = 0
  · simp [z]
  have := Nat.log2_self_le (n := n) (by omega)
  by_contra! h
  have := Nat.pow_le_pow_right (n := 2) (by decide) (show 63 ≤ n.log2 by omega)
  dsimp [maxLeaves] at hn
  omega

/-- The extracted unsigned integer logarithm returns the natural binary logarithm. -/
theorem log_ok (x : Std.U64) (positive : 0 < x.val) (small : x.val ≤ maxLeaves + 1) :
    ∃ z : Std.U32, CoreModels.core.num.U64.ilog2 x = RustM.ok z ∧ z.val = x.val.log2 := by
  refine ⟨⟨BitVec.ofNat 32 x.val.log2⟩, ?_, ?_⟩
  · simp [CoreModels.core.num.U64.ilog2, rust_primitives.arithmetic.ilog2_u64, uilog2,
      Nat.ne_of_gt positive]
  · change x.val.log2 % 2 ^ 32 = _
    have := logBound small
    omega

/-- A u32 widens to u64 without changing its value. -/
theorem castUp (x : Std.U32) : (UScalar.cast .U64 x).val = x.val := by
  simp [UScalar.cast_val_eq]
  scalar_tac

private theorem castDown (x : Std.U64) (small : x.val < 2 ^ 32) :
    (UScalar.cast .U32 x).val = x.val := by
  simp [UScalar.cast_val_eq]
  omega

/-- Position at the birth of a leaf or its paired parent, including every checked u64 operation. -/
theorem birth_position (x : Std.U64) (isLeaf : Bool) (bound : x.val ≤ maxLeaves) :
    ∃ p, birthed_node_pos x isLeaf = RustM.ok p ∧
      p.val = 2 * x.val - (x.val + 1).log2 + (if isLeaf then 0 else 1) := by
  obtain ⟨d, hd, vd⟩ := mul_ok (2#u64) x (by dsimp [maxLeaves] at bound; scalar_tac)
  obtain ⟨n, hn, vn⟩ := add_ok x 1#u64 (by dsimp [maxLeaves] at bound; scalar_tac)
  change d.val = 2 * x.val at vd
  change n.val = x.val + 1 at vn
  obtain ⟨k, hk, vk⟩ := log_ok n (by omega) (by omega)
  have enough : (x.val + 1).log2 ≤ d.val := by
    by_cases h : x.val = 0
    · simp [h]
    · have := Nat.log2_le_self (x.val + 1)
      omega
  obtain ⟨base, hb, vb⟩ := sub_ok d (UScalar.cast .U64 k) (by rw [castUp, vk, vn]; exact enough)
  have loc : location_to_position x = RustM.ok base := by
    simp [location_to_position, hd, hn, hk, hb, lift]
  rw [castUp, vk, vn] at vb
  cases isLeaf with
  | true => exact ⟨base, by simpa [birthed_node_pos] using loc, by simp_all⟩
  | false =>
    obtain ⟨p, hp, vp⟩ := add_ok base 1#u64 (by dsimp [maxLeaves] at bound; scalar_tac)
    exact ⟨p, by simp [birthed_node_pos, loc, hp], by change p.val = base.val + 1 at vp; simp_all⟩

/-- Birth leaf of the subtree starting at start, before conversion to a physical position. -/
def birth (start h : Nat) : Nat :=
  let last := start + 2 ^ h - 1
  if h = 0 then last else last + 2 ^ (h - 1) - 1

/-- Read the extracted delayed-merge birth calculation. -/
theorem birth_ok (last : Std.U64) (h : Std.U32) (start : Nat)
    (atLast : last.val = start + 2 ^ h.val - 1) (height : h.val ≤ 62)
    (room : last.val ≤ maxLeaves) :
    ∃ b, peak_birth_leaf last h = RustM.ok b ∧ b.val = birth start h.val := by
  by_cases z : h = 0#u32
  · subst h
    exact ⟨last, by simp [peak_birth_leaf], by simpa [birth] using atLast⟩
  · have pos : 0 < h.val := by
      by_contra! le
      exact z (UScalar.eq_of_val_eq (by scalar_tac))
    obtain ⟨k, hk, vk⟩ := sub_ok h 1#u32 (by scalar_tac)
    change k.val = h.val - 1 at vk
    obtain ⟨w, hw, vw⟩ := pow_ok k (by omega)
    have upper := Nat.pow_le_pow_right (n := 2) (by decide) (show k.val ≤ 61 by omega)
    have nonzero := Nat.two_pow_pos k.val
    obtain ⟨t, ht, vt⟩ := add_ok last w (by dsimp [maxLeaves] at room; scalar_tac)
    obtain ⟨b, hb, vb⟩ := sub_ok t 1#u64 (by scalar_tac)
    exact ⟨b, by simp [peak_birth_leaf, z, hk, hw, ht, hb], by
      simp [birth, Nat.ne_of_gt pos, vb, vt, vw, vk, atLast]⟩

/-- The cursor at the head of the k remaining peaks. For an exhausted nonempty iterator
the last decrement has wrapped the index; the guard inspects only remaining. -/
structure Cursor (it : PeakIterator) (n k start : Nat) : Prop where
  /-- The stored MMB leaf count. -/
  count : it.n.val = n
  /-- The exact remaining count. -/
  remaining : it.remaining.val = k
  /-- The Rust bit index including wraparound. -/
  index : it.current_i.val = if k = 0 then (if n = 0 then 0 else 2 ^ 32 - 1) else k - 1
  /-- First leaf of the next peak. -/
  startAt : it.start_leaf_cursor.val = start
  /-- Remaining peaks span exactly the suffix. -/
  extent : start + leftWidth (n + 1) k = n
  /-- Every remaining peak starts on its power-of-two boundary. -/
  aligned : 2 ^ k ∣ start
  /-- The bit index never exceeds the initial count. -/
  limit : k ≤ (n + 1).log2

/-- Initialization from the valid leaf count, including the default empty iterator. -/
theorem initialized (n : Std.U64) (valid : n.val ≤ maxLeaves) :
    ∃ it, PeakIterator.new n = RustM.ok it ∧ Cursor it n.val (n.val + 1).log2 0 := by
  by_cases zero : n = 0#u64
  · subst n
    exact ⟨⟨0#u64, 0#u32, 0#u32, 0#u64⟩, by simp [PeakIterator.new,
      PeakIterator.Insts.CoreDefaultDefault.default,
      CoreModels.core.U64.Insts.CoreDefaultDefault.default,
      CoreModels.core.U32.Insts.CoreDefaultDefault.default],
      ⟨rfl, rfl, rfl, rfl, rfl, dvd_zero _, le_rfl⟩⟩
  have positive : n.val ≠ 0 := fun eq => zero (UScalar.eq_of_val_eq eq)
  obtain ⟨u, hu, vu⟩ := add_ok n 1#u64 (by dsimp [maxLeaves] at valid; scalar_tac)
  change u.val = n.val + 1 at vu
  obtain ⟨k, hk, vk⟩ := log_ok u (by omega) (by omega)
  rw [vu] at vk
  have kPos : 0 < (n.val + 1).log2 := by
    have h := Nat.lt_log2_self (n := n.val + 1)
    by_contra! hz
    have z : (n.val + 1).log2 = 0 := by omega
    rw [z] at h
    omega
  obtain ⟨i, hi, vi⟩ := sub_ok k 1#u32 (by scalar_tac)
  refine ⟨⟨n, i, k, 0#u64⟩, by simp [PeakIterator.new, zero, hu, hk, hi], ?_⟩
  exact ⟨rfl, vk, by simp [kPos.ne', vi, vk], rfl, by simp [width_all], dvd_zero _, le_rfl⟩

private theorem shift_bit (u : Std.U64) (i : Std.U32) (small : i.val < 64) :
    ∃ v : Std.U64, u >>> i = RustM.ok v ∧ (v &&& 1#u64).val = u.val / 2 ^ i.val % 2 := by
  obtain ⟨v, hv, value, -, -⟩ := ok_of_partialSpec (UScalar.ShiftRight_spec u i)
    (by intro e; cases e <;> simp; omega) (by simp)
  refine ⟨v, hv, ?_⟩
  rw [UScalar.val_and, value, Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

private theorem pow64 (h : Std.U64) (small : h.val < 64) :
    ∃ w : Std.U64, 1#u64 <<< h = RustM.ok w ∧ w.val = 2 ^ h.val := by
  obtain ⟨w, hw, value, -, -⟩ := ok_of_partialSpec (UScalar.ShiftLeft_spec (1#u64) h _ rfl)
    (by intro e; cases e <;> simp; omega) (by simp)
  refine ⟨w, hw, ?_⟩
  rw [value, show (1#u64).val = 1 from rfl, Nat.one_shiftLeft, Nat.mod_eq_of_lt]
  simpa [UScalar.size, U64.size, U64.numBits] using
    (Nat.pow_lt_pow_right (a := 2) (by decide) small)

/-- The delayed birth of the next peak falls strictly inside the current snapshot. -/
theorem birth_inside {start n i : Nat} (full : start + leftWidth (n + 1) (i + 1) = n) :
    birth start (peakHeight (n + 1) i) < n := by
  let h := peakHeight (n + 1) i
  have height : h ≤ i + 1 := by dsimp [h, peakHeight]; omega
  have eq := width_step (n + 1) i
  change leftWidth (n + 1) (i + 1) = 2 ^ h + leftWidth (n + 1) i at eq
  have tail : 2 ^ i - 1 ≤ leftWidth (n + 1) i := by simp [leftWidth]
  have pos := Nat.two_pow_pos h
  have small := Nat.pow_le_pow_right (n := 2) (by decide) (show h - 1 ≤ i by omega)
  change birth start h < n
  simp only [birth]
  split <;> omega

/-- Every nonterminal call yields exactly the next height and its physical root position,
advances the leaf cursor by that peak's width, and returns the correct next machine state. -/
theorem next_peak {it : PeakIterator} {n i start : Nat} (valid : n ≤ maxLeaves)
    (c : Cursor it n (i + 1) start) :
    ∃ (p : Std.U64) (h : Std.U32) (next : PeakIterator),
      PeakIterator.next it = RustM.ok (.Some (p, h), next) ∧
      h.val = peakHeight (n + 1) i ∧ p.val = subtreePosition start h.val ∧
      Cursor next n i (start + 2 ^ h.val) := by
  let height := peakHeight (n + 1) i
  have count := c.count
  have rem := c.remaining
  have idx : it.current_i.val = i := by simpa using c.index
  have cur := c.startAt
  have left := c.limit
  have whole := c.extent
  have bound := logBound (n := n + 1) (by omega)
  have nz : it.remaining ≠ 0#u32 := by intro z; rw [z] at rem; scalar_tac
  obtain ⟨u, hu, vu⟩ := add_ok it.n 1#u64 (by dsimp [maxLeaves] at valid; scalar_tac)
  change u.val = it.n.val + 1 at vu
  obtain ⟨shift, hs, vs⟩ := shift_bit u it.current_i (by omega)
  rw [vu, count, idx] at vs
  have hBound : height ≤ i + 1 := by dsimp [height, peakHeight]; omega
  obtain ⟨h, hh, vh⟩ := add_ok (UScalar.cast .U64 it.current_i) (shift &&& 1#u64)
    (by rw [castUp, idx, vs]; scalar_tac)
  rw [castUp, idx, vs] at vh
  change h.val = height at vh
  obtain ⟨w, hw, vw⟩ := pow64 h (by omega)
  rw [vh] at vw
  have extent : start + 2 ^ height + leftWidth (n + 1) i = n := by
    simpa [height, width_step (n + 1) i, Nat.add_assoc] using whole
  obtain ⟨cursor, hc, vc⟩ := add_ok it.start_leaf_cursor w (by
    dsimp [maxLeaves] at valid; scalar_tac)
  rw [cur, vw] at vc
  have power := Nat.two_pow_pos height
  obtain ⟨last, hl, vl⟩ := sub_ok cursor 1#u64 (by scalar_tac)
  change last.val = cursor.val - 1 at vl
  have as32 := castDown h (by omega)
  let h32 := UScalar.cast .U32 h
  have vh32 : h32.val = height := as32.trans vh
  obtain ⟨b, hb, vb⟩ := birth_ok last h32 start (by rw [vh32, vl, vc]) (by omega) (by omega)
  have inside := birth_inside whole
  change birth start height < n at inside
  rw [vh32] at vb
  obtain ⟨p, hp, vp⟩ := birth_position b (decide (h = 0#u64)) (by omega)
  obtain ⟨rem', hr, vr⟩ := sub_ok it.remaining 1#u32 (by scalar_tac)
  let idx' := Aeneas.Std.U32.wrapping_sub it.current_i 1#u32
  have wrapped : CoreModels.core.num.U32.wrapping_sub it.current_i 1#u32 = RustM.ok idx' := rfl
  let next : PeakIterator := ⟨it.n, idx', rem', cursor⟩
  refine ⟨p, h32, next, ?_, vh32, ?_, ?_⟩
  · dsimp [h32] at hb
    simp [PeakIterator.next, nz, hu, hs, hh, hw, hc, hl, hr, wrapped, lift, next, h32, hb, hp]
  · have hz : (h = 0#u64) ↔ height = 0 := by
      refine ⟨fun eq => by rw [← vh, eq]; rfl, fun eq => UScalar.eq_of_val_eq (vh.trans eq)⟩
    simpa [subtreePosition, birth, vh32, hz, vb] using vp
  · have idxNext : idx'.val = if i = 0 then 2 ^ 32 - 1 else i - 1 := by
      simp only [idx', U32.wrapping_sub_val_eq, idx]
      simp only [UScalar.size]
      change (i + 4294967295) % 4294967296 = _
      split <;> omega
    have nonempty : n ≠ 0 := by rintro rfl; simp at left
    refine ⟨count, by simp [next, vr, rem], ?_, by simpa [next, vh32] using vc,
      by simpa [vh32] using extent, ?_, by omega⟩
    · simpa [next, nonempty] using idxNext
    · rw [vh32]
      apply dvd_add
      · exact dvd_trans (pow_dvd_pow _ (by omega : i ≤ i + 1)) c.aligned
      · exact pow_dvd_pow _ (show i ≤ height by dsimp [height, peakHeight]; omega)

/-- On the exhausted cursor, every further call returns None without changing state. -/
theorem done_next {it : PeakIterator} {n start : Nat} (c : Cursor it n 0 start) :
    PeakIterator.next it = RustM.ok (.None, it) ∧ start = n := by
  have rem : it.remaining = 0#u32 := UScalar.eq_of_val_eq c.remaining
  exact ⟨by simp [PeakIterator.next, rem], by simpa [leftWidth, Nat.mod_one] using c.extent⟩

/-- Pair each planned peak's physical position with its height in iteration order. -/
def located (start : Nat) : List Nat → List (Nat × Nat)
  | [] => []
  | h :: hs => (subtreePosition start h, h) :: located (start + 2 ^ h) hs

/-- The sequence actually returned by repeated calls to the extracted Rust method. -/
inductive Yields : PeakIterator → List (Nat × Nat) → PeakIterator → Prop where
  /-- The iterator is exhausted and remains at its final cursor. -/
  | stop {it} (done : PeakIterator.next it = RustM.ok (.None, it)) : Yields it [] it
  /-- Emit one actual successful Rust result and then visit the tail. -/
  | step {it next final : PeakIterator} {h : Std.U32} {p : Std.U64} {rest}
      (emit : PeakIterator.next it = RustM.ok (.Some (p, h), next))
      (tail : Yields next rest final) : Yields it ((p.val, h.val) :: rest) final

private theorem complete {n k start : Nat} {it : PeakIterator} (valid : n ≤ maxLeaves)
    (cursor : Cursor it n k start) :
    ∃ last, Yields it (located start (peakHeights (n + 1) k)) last ∧ Cursor last n 0 n := by
  induction k generalizing start it with
  | zero =>
    obtain ⟨done, rfl⟩ := done_next cursor
    exact ⟨it, .stop done, cursor⟩
  | succ k ih =>
    obtain ⟨p, h, next, emit, height, pos, cur⟩ := next_peak valid cursor
    obtain ⟨last, tail, finished⟩ := ih cur
    have step := Yields.step emit tail
    exact ⟨last, by simpa [peakHeights, located, pos, height] using step, finished⟩

/-- On every valid leaf count the extracted iterator enumerates exactly all peaks used by
the verifier, with the first leaf cursor at zero and the exhausted cursor at the leaf count. -/
theorem all_peaks (n : Std.U64) (valid : n.val ≤ maxLeaves) :
    ∃ init last, PeakIterator.new n = RustM.ok init ∧ Cursor init n.val (n.val + 1).log2 0 ∧
      Yields init (located 0 (heights n.val)) last ∧ Cursor last n.val 0 n.val := by
  obtain ⟨it, ok, c⟩ := initialized n valid
  obtain ⟨last, seq, fin⟩ := complete valid c
  exact ⟨it, last, ok, c, seq, fin⟩

end
end Qmdb.Mmb.Peaks
