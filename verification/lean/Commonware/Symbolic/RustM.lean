module
public import Aeneas
public import CoreModels

/-! Machine arithmetic and monadic plumbing for any extracted Rust: an operation returns `ok` when
its bounds hold, and `ok` results can be read back from binds and matches. Checked by Lean. -/

namespace Commonware.Symbolic
open Aeneas Aeneas.Std Aeneas.Std.WP CoreModels
@[expose] public section

theorem ok_of_partialSpec {α} {x : RustM α} {p : α → Prop} {pf : Error → Prop} {pd : Prop}
    (h : partialSpec x p pf pd) (hf : ∀ e, ¬ pf e) (hd : ¬ pd) : ∃ a, x = RustM.ok a ∧ p a := by
  cases x with
  | ret a => exact ⟨a, rfl, by simpa using h⟩
  | vis i k => cases i with | fail e => simp [partialSpec] at h; exact absurd h (hf e)
  | div => simp [partialSpec] at h; exact absurd h hd

theorem ok_of_spec {α} {x : RustM α} {p : α → Prop} (h : spec x p) : ∃ a, x = RustM.ok a ∧ p a := by
  cases x with
  | ret a => exact ⟨a, rfl, (spec_ok a).mp h⟩
  | vis i k => exact absurd h (by simp [spec_vis])
  | div => exact absurd h (by simp [spec_div])

theorem add_ok {ty} (x y : UScalar ty) (bound : x.val + y.val ≤ UScalar.max ty) :
    ∃ z, x + y = RustM.ok z ∧ z.val = x.val + y.val :=
  ok_of_partialSpec UScalar.add_spec (by intro e; cases e <;> simp; omega) (by simp)

theorem sub_ok {ty} (x y : UScalar ty) (bound : y.val ≤ x.val) :
    ∃ z, x - y = RustM.ok z ∧ z.val = x.val - y.val := by
  obtain ⟨z, hz, hv, -⟩ :=
    ok_of_partialSpec UScalar.sub_spec (by intro e; cases e <;> simp; omega) (by simp)
  exact ⟨z, hz, hv⟩

theorem mul_ok {ty} (x y : UScalar ty) (bound : x.val * y.val ≤ UScalar.max ty) :
    ∃ z, x * y = RustM.ok z ∧ z.val = x.val * y.val :=
  ok_of_spec (UScalar.mul_spec bound)

theorem pow_ok (h : Std.U32) (bound : h.val ≤ 63) :
    ∃ z : Std.U64, 1#u64 <<< h = RustM.ok z ∧ z.val = 2 ^ h.val := by
  obtain ⟨z, hz, hv, -, -⟩ := ok_of_partialSpec (UScalar.ShiftLeft_spec (1#u64) h _ rfl)
    (by intro e; cases e <;> simp; omega) (by simp)
  refine ⟨z, hz, ?_⟩
  rw [hv]
  have : (1#u64).val = 1 := rfl
  rw [this, Nat.one_shiftLeft]
  apply Nat.mod_eq_of_lt
  have : 2 ^ h.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  simpa [UScalar.size, U64.size, U64.numBits] using this

theorem len_ok {α} (s : Slice α) : core.slice.Slice.len s = RustM.ok (Slice.len s) := by
  simp [core.slice.Slice.len, rust_primitives.slice.slice_length]

theorem succ_ok (i : Std.Usize) {α} (s : Slice α) (bound : i.val < s.length) :
    ∃ z, i + 1#usize = RustM.ok z ∧ z.val = i.val + 1 := by
  have := Slice.length_ineq s
  exact add_ok i 1#usize (by scalar_tac)

theorem ok_inj {α} {x y : α} (h : RustM.ok x = RustM.ok y) : x = y := by
  have := congrArg RustM.match h
  simpa using this

theorem bind_eq_ok {α β} {x : RustM α} {f : α → RustM β} {b : β}
    (h : Std.bind x f = RustM.ok b) : ∃ a, x = RustM.ok a ∧ f a = RustM.ok b := by
  cases x with
  | ret a => exact ⟨a, rfl, by simpa using h⟩
  | vis i k =>
    rw [bind_vis] at h
    have := congrArg RustM.match h
    simp at this
  | div =>
    rw [bind_div] at h
    have := congrArg RustM.match h
    simp at this

theorem eq_ok_of_match {α} {x : RustM α} {a : α} (h : x.match = .ok a) : x = RustM.ok a := by
  cases x with
  | ret b => simp at h; rw [h]
  | vis i k => simp at h
  | div => simp at h

/-- A loop whose body continues runs on from the state that the body returns. -/
theorem loop_cont {α β} (body : α → RustM (ControlFlow α β)) (x x' : α)
    (h : body x = RustM.ok (.cont x')) : loop body x = loop body x' := by
  rw [loop.eq_def, h]
  simp

/-- A loop whose body is done returns what the body returns. -/
theorem loop_done {α β} (body : α → RustM (ControlFlow α β)) (x : α) (y : β)
    (h : body x = RustM.ok (.done y)) : loop body x = RustM.ok y := by
  rw [loop.eq_def, h]
  simp

end
end Commonware.Symbolic
