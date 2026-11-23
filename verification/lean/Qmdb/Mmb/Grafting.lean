module
import all Aeneas.Std.Scalar.OverflowingOps.Add
public import Qmdb.Mmb.Pinned
public import Qmdb.Mmb.Plan
public import Qmdb.Bitmap

/-! Activity evidence for the three chunk placements in Tempo's pinned MMB. -/

namespace Qmdb.Mmb
open Aeneas Aeneas.Std CoreModels Commonware.Symbolic pinned_dfs
@[expose] public section

/-- For the first height-eight subtree, the 256th leaf precedes its birth by 127 insertions. -/
theorem first_graft_birth : birth_size 0#u64 8#u32 = RustM.ok 383#u64 := by
  have sub : 8#u32 - 1#u32 = RustM.ok 7#u32 := by rfl
  simp +decide [birth_size, sub, CoreModels.core.num.U64.checked_shl,
    CoreModels.core.option.Option.expect,
    CoreModels.core.num.U64.checked_add, CoreModels.core.option.Option.and_then,
    birth_size.closure.Insts.CoreOpsFunctionFnOnceTupleU64OptionU64.call_once,
    CoreModels.core.num.U64.checked_sub, CoreModels.core.num.U64.overflowing_add,
    CoreModels.core.num.U64.overflowing_sub, rust_primitives.arithmetic.overflowing_add_u64,
    rust_primitives.arithmetic.overflowing_sub_u64, uoverflowing_sub, UScalar.overflowing_add]

/-- For every 64-bit leaf count, the resolved chunk count matches the pinned-size calculation. -/
theorem resolved_eq (leaves : Std.U64) :
    ∃ count, resolved leaves 8#u32 383#u64 = RustM.ok count ∧
      count.val = graftedChunks leaves.val := by
  by_cases small : leaves < 383#u64
  · refine ⟨0#u64, by simp [resolved, small], ?_⟩
    change leaves.val < 383 at small
    simp [graftedChunks, small]
  · have ge : 383 ≤ leaves.val := by
      change ¬leaves.val < 383 at small
      omega
    obtain ⟨diff, hd, dv⟩ := sub_ok leaves 383#u64 ge
    have shift : 1#u64 <<< 8#u32 = RustM.ok 256#u64 := by rfl
    obtain ⟨q, hq, qv⟩ := UScalar.div_spec diff (y := 256#u64) (by decide)
    change q.val = diff.val / 256 at qv
    change diff.val = leaves.val - 383 at dv
    have lim : leaves.val ≤ UScalar.max .U64 := by scalar_tac
    have room : q.val + 1 ≤ UScalar.max .U64 := by omega
    obtain ⟨result, hr, rv⟩ := add_ok q 1#u64 room
    refine ⟨result, by simp [resolved, small, shift, hd, hq, hr], ?_⟩
    simp [graftedChunks, show ¬leaves.val < 383 by omega, rv, qv, dv]

/-- Exactly the complete prefix minus at most the single pending chunk is grafted. -/
theorem grafted_bounds (n : Nat) :
    graftedChunks n ≤ n / 256 ∧ n / 256 ≤ graftedChunks n + 1 := by
  unfold graftedChunks
  split <;> omega

/-- The first-chunk birth calculation and the range verifier's minimum and presence checks
agree with the planner at every machine leaf count. -/
theorem pinned_placement (leaves : Std.U64) :
    ∃ count, (do
      let first ← birth_size 0#u64 8#u32
      resolved leaves 8#u32 first) = RustM.ok count ∧
      min count.val (leaves.val / 256) = graftedChunks leaves.val ∧
      (leaves.val / 256 - count.val = 1 ↔ graftedChunks leaves.val < leaves.val / 256) := by
  obtain ⟨count, eq, val⟩ := resolved_eq leaves
  obtain ⟨upper, lower⟩ := grafted_bounds leaves.val
  refine ⟨count, by simp [first_graft_birth, eq], by simp [val, upper], ?_⟩
  omega

/-- Every in-range operation lies in a grafted, pending, or partial chunk, including when
the final two chunks are simultaneously present. -/
theorem placement_exhaustive {n loc : Nat} (inside : loc < n) :
    loc / 256 < graftedChunks n ∨
    (loc / 256 = graftedChunks n ∧ loc / 256 < n / 256) ∨
    (loc / 256 = n / 256 ∧ n % 256 ≠ 0) := by
  obtain ⟨_, _⟩ := grafted_bounds n
  omega

private abbrev iter := CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT
  Std.U8
private abbrev fn := graft.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool
private abbrev body (st : Slice Std.U8 × Unit) :
    RustM (ControlFlow (Slice Std.U8 × Unit) (Bool × Slice Std.U8)) :=
  core.iter.traits.iterator.iter_all_loop.body iter fn st.1 st.2

private theorem body_nil (s : Slice Std.U8) (hs : s.val = []) :
    body (s, ()) = RustM.ok (.done (true, s)) := by
  have zero : s.len = 0#usize := UScalar.eq_of_val_eq (by simp [Slice.len, hs])
  simp [body, core.iter.traits.iterator.iter_all_loop.body,
    CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    rust_primitives.sequence.seq_len, zero]
  erw [bind_ok]
  rfl

private theorem body_cons (s : Slice Std.U8) (a : Std.U8) (l : List Std.U8) (hs : s.val = a :: l) :
    ∃ tail : Slice Std.U8, tail.val = l ∧ body (s, ()) = RustM.ok
      (if a = 0#u8 then .cont (tail, ()) else .done (false, tail)) := by
  have len : s.len ≠ 0#usize := by
    intro eq
    have := congrArg UScalar.val eq
    simp [Slice.len, hs] at this
  let tail := Slice.from l (by have := s.property; rw [hs] at this; simp at this; omega)
  refine ⟨tail, by simp [tail, Slice.from_val], ?_⟩
  have next : iter.next s = RustM.ok (some a, tail) := by
    simp [CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len, len, rust_primitives.sequence.seq_remove, hs, tail]
    rfl
  change CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next s =
    RustM.ok (some a, tail) at next
  by_cases eq : a = 0#u8 <;>
    simp [body, core.iter.traits.iterator.iter_all_loop.body, next, eq,
      graft.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool.call_mut]

private theorem all_zero (xs : List Std.U8) : ∀ s : Slice Std.U8, s.val = xs →
    ∃ rest : Slice Std.U8,
      loop body (s, ()) = RustM.ok (xs.all (fun b => decide (b = 0#u8)), rest) := by
  induction xs with
  | nil =>
    intro s eq
    exact ⟨s, loop_done body (s, ()) _ (body_nil s eq)⟩
  | cons a l ih =>
    intro s eq
    obtain ⟨tail, ht, head⟩ := body_cons s a l eq
    by_cases zero : a = 0#u8
    · obtain ⟨rest, loopEq⟩ := ih tail ht
      refine ⟨rest, ?_⟩
      rw [loop_cont body (s, ()) (tail, ()) (by simpa only [zero, ↓reduceIte] using head)]
      simpa [zero] using loopEq
    · exact ⟨tail, by
        simpa [zero] using loop_done body (s, ()) (false, tail) (by simpa [zero] using head)⟩

/-- The unmodified pinned zero-chunk guard returns the subtree itself exactly when all bytes
are zero. Otherwise the two hash inputs are the supplied chunk followed by the subtree. -/
theorem pinned_graft (chunk ops : Slice Std.U8) :
    graft chunk ops = RustM.ok (if chunk.val.all (fun b => decide (b = 0#u8)) then
      pinned_dfs.Trace.Unwrapped ops else pinned_dfs.Trace.Hash chunk ops) := by
  obtain ⟨rest, eq⟩ := all_zero chunk.val chunk rfl
  unfold graft
  simp [CoreModels.core.slice.Slice.iter, rust_primitives.sequence.seq_from_slice,
    CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all,
    core.iter.traits.iterator.Iterator.all.default, core.iter.traits.iterator.iter_all,
    core.iter.traits.iterator.iter_all_loop]
  erw [bind_ok]
  erw [eq]
  erw [bind_ok]
  change (if chunk.val.all (fun b => decide (b = 0#u8)) then RustM.ok (Trace.Unwrapped ops)
    else RustM.ok (Trace.Hash chunk ops)) = _
  simp only [List.all_eq_true, decide_eq_true_eq]
  split <;> rfl

/-- The pinned guard agrees with the vector equality used by the ideal graft model. Both
branches preserve exactly the arguments hashed by the caller. -/
theorem pinned_graft_chunk (c : Active.Chunk) (ops : Slice Std.U8) :
    graft (Active.Chunk.asSlice c) ops = RustM.ok
      (if c = Vector.replicate 32 0 then Trace.Unwrapped ops
       else Trace.Hash (Active.Chunk.asSlice c) ops) := by
  rw [pinned_graft]
  by_cases zero : c = Vector.replicate 32 0
  · subst c
    simp [Active.Chunk.asSlice, Slice.from_val]
    rfl
  · have nz : ¬∀ x ∈ (Active.Chunk.asSlice c).val, x = 0#u8 := by
      intro allZero
      apply zero
      apply Vector.ext
      intro i hi
      have mem : c[i] ∈ c.toList := by simp
      have m : (⟨c[i].toBitVec⟩ : Std.U8) ∈ (Active.Chunk.asSlice c).val := by
        simp only [Active.Chunk.asSlice, Slice.from_val, List.mem_map]
        exact ⟨c[i], mem, rfl⟩
      have bitEq := congrArg UScalar.bv (allZero _ m)
      apply UInt8.toBitVec_inj.mp
      simpa using bitEq
    simp [zero, nz]

end
end Qmdb.Mmb
