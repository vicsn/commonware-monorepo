module
public import Reference

/-! Proofs that the extracted production traversal, adapter and client step, interpreted with
`dyTerms`, compute exactly what the reference model computes, and that the production verifier
is binding. Checked by Lean; nothing here is trusted beyond the statements that `Protocol` and
`SecurityTheorems` use. -/

namespace Qmdb.Correspondence
open DY Aeneas Aeneas.Std Aeneas.Std.WP CoreModels qmdb_dylean
@[expose] public section

/-! ## Machine arithmetic -/

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
    ∃ z : Std.U64, 1#u64 <<< h = RustM.ok z ∧ z.val = 2^h.val := by
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

theorem index_ok {α} (s : Slice α) (i : Std.Usize) (bound : i.val < s.length) :
    Slice.index_usize s i = RustM.ok s.val[i.val] := by
  obtain ⟨x, hx, _, rfl⟩ := ok_of_partialSpec (Slice.index_usize_spec s i)
    (by intro e; cases e <;> simp; omega) (by simp)
  exact hx

theorem succ_ok (i : Std.Usize) {α} (s : Slice α) (bound : i.val < s.length) :
    ∃ z, i + 1#usize = RustM.ok z ∧ z.val = i.val + 1 := by
  have := Slice.length_ineq s
  exact add_ok i 1#usize (by scalar_tac)

/-! ## Digests -/

private def byte (v : Std.U64) (k : Nat) : Std.U8 :=
  UScalar.cast .U8 (⟨v.bv.ushiftRight k⟩ : Std.U64)

private theorem be64_ok (v : Std.U64) : adapter.be64 v = RustM.ok (Array.make 8#usize
    [byte v 56, byte v 48, byte v 40, byte v 32, byte v 24, byte v 16, byte v 8,
      UScalar.cast .U8 v]) := by
  unfold adapter.be64
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight, lift]
  simp [byte]

private theorem ofNat_mod (x : Nat) : UInt8.ofNat (x % 256) = UInt8.ofNat x := by
  apply UInt8.toNat_inj.mp
  simp

private theorem ofNat_byte (v : Std.U64) (k : Nat) :
    UInt8.ofNat (byte v k).val = UInt8.ofNat (v.val / 2^k) := by
  simp only [byte, UScalar.cast_val_eq]
  rw [show (2:Nat)^(UScalarTy.U8.numBits) = 256 by rfl, ofNat_mod]
  congr 1
  change (v.bv.ushiftRight k).toNat = v.bv.toNat / 2^k
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem be64_bytes (v : Std.U64) : toByteArray (Array.to_slice (Array.make 8#usize
    [byte v 56, byte v 48, byte v 40, byte v 32, byte v 24, byte v 16, byte v 8,
      UScalar.cast .U8 v])) = be64 v.val := by
  simp [toByteArray, be64, Array.val_to_slice, List.range_succ, ofNat_byte, ofNat_mod]

private theorem wrap_bytes (v : Std.U64) : toByteArray (Array.to_slice (Array.make 10#usize
    [adapter.MMR_DOMAIN, adapter.FORWARD_FOLD, byte v 56, byte v 48, byte v 40, byte v 32, byte v 24,
      byte v 16, byte v 8, UScalar.cast .U8 v])) = ⟨#[0,0]⟩ ++ be64 v.val := by
  rw [← be64_bytes]
  apply ByteArray.ext
  simp [toByteArray, Array.val_to_slice, adapter.MMR_DOMAIN, adapter.FORWARD_FOLD]

theorem leaf_eq (p : Std.U64) (item : ByteArray) :
    adapter.leaf dyTerms p item = RustM.ok (leaf p.val item) := by
  simp only [adapter.leaf, be64_ok, core.array.Array.as_slice, rust_primitives.slice.array_as_slice]
  simp [dyTerms, leaf, be64_bytes]

theorem node_eq (p : Std.U64) (l r : Bytes) :
    adapter.node dyTerms p l r = RustM.ok (node p.val l r) := by
  simp only [adapter.node, be64_ok, core.array.Array.as_slice, rust_primitives.slice.array_as_slice]
  simp [dyTerms, node, be64_bytes]

theorem wrap_eq (h : Std.U32) (bound : h.val ≤ 63) (peak : Bytes) :
    adapter.wrap dyTerms h peak = RustM.ok (wrap h.val peak) := by
  obtain ⟨z, hz, hv⟩ := pow_ok h bound
  simp only [adapter.wrap, hz, be64_ok, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice]
  simp [Array.index_usize, dyTerms, wrap]
  rw [wrap_bytes, hv]

/-! ## Single-item verification -/

theorem eq_ok (a b : Bytes) : dyTerms.corecmpPartialEqInst.eq a b = RustM.ok (decide (a = b)) :=
  rfl

/-! ## The production traversal -/

abbrev Opening := adapter.Opening Unit Bytes Bytes ByteArray

abbrev backend := adapter.Opening.Insts.Qmdb_dyleanTraversalBackend dyTerms

/-- The traversal's result agrees with the model's, and its cursor marks the model's unread
siblings. -/
def Traversed (item : ByteArray) (sib : Slice Bytes) :
    (CoreModels.core.result.Result Bytes traversal.Error × Opening) →
      Option (Bytes × List Bytes) → Prop
  | (.Ok d, o), some (d', rest) =>
    d = d' ∧ o.item = item ∧ o.siblings = sib ∧ o.next.val ≤ sib.length ∧
      rest = sib.val.drop o.next.val
  | (.Err _, _), none => True
  | _, _ => False

theorem sibling_ok (o : Opening) (room : o.next.val < o.siblings.length) :
    ∃ n1 : Std.Usize, adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling dyTerms o =
      RustM.ok (.Ok o.siblings.val[o.next.val], { o with next := n1 }) ∧ n1.val = o.next.val + 1 := by
  obtain ⟨n1, hn1, n1v⟩ := succ_ok o.next o.siblings room
  have lt : o.next < Slice.len o.siblings := by scalar_tac
  refine ⟨n1, ?_, n1v⟩
  have roomv : o.next.val < o.siblings.val.length := room
  simp [adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling, len_ok, roomv,
    index_ok o.siblings o.next room, hn1]

theorem sibling_end (o : Opening) (none_left : ¬ o.next.val < o.siblings.length) :
    adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling dyTerms o = RustM.ok (.Err .MissingDigests, o) := by
  have nlt : ¬ o.next < Slice.len o.siblings := by scalar_tac
  have endv : ¬ o.next.val < o.siblings.val.length := none_left
  simp [adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling, len_ok, endv]

/-- A subtree outside the queried range is read as one sibling. -/
theorem outside (o : Opening) (p w s loc e : Std.U64) (bound : s.val + w.val ≤ 2^63)
    (off : s.val + w.val ≤ loc.val ∨ e.val ≤ s.val) :
    traversal.reconstruct backend o p w s loc e = adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling dyTerms o := by
  obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
  rw [traversal.reconstruct.eq_def]
  simp only [hstop, bind_ok]
  by_cases before : s.val + w.val ≤ loc.val
  · have : stop ≤ loc := by scalar_tac
    simp [this]
  · have after : s ≥ e := by scalar_tac
    have : ¬ stop ≤ loc := by scalar_tac
    simp [this, after]

theorem traverse_eq (item : ByteArray) (sib : Slice Bytes) :
    ∀ (H : Nat) (p w s loc e : Std.U64) (o : Opening), w.val = 2^H → H ≤ 63 →
      2*(w.val-1) ≤ p.val → s.val + w.val ≤ 2^63 → s.val ≤ loc.val → loc.val < s.val + w.val →
      e.val = loc.val + 1 → o.item = item → o.siblings = sib → o.next.val ≤ sib.length →
      ∃ r, traversal.reconstruct backend o p w s loc e = RustM.ok r ∧
        Traversed item sib r (replay item H p.val s.val loc.val (sib.val.drop o.next.val)) := by
  intro H
  induction H with
  | zero =>
    intro p w s loc e o width _ _ _ low high finish hitem hsib cursor
    simp at width
    obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
    have c1 : ¬ stop.val ≤ loc.val := by scalar_tac
    have c2 : ¬ e.val ≤ s.val := by scalar_tac
    have c3 : w = 1#u64 := by scalar_tac
    refine ⟨(.Ok (leaf p.val item), o), ?_, ?_⟩
    · rw [traversal.reconstruct.eq_def]
      simp only [hstop, bind_ok]
      simp [c1, c2, c3, adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.leaf, leaf_eq, hitem]
    · simp [replay, Traversed, hitem, hsib, cursor]
  | succ n ih =>
    intro p w s loc e o width bound position start low high finish hitem hsib cursor
    have one : 1 ≤ 2^n := Nat.one_le_two_pow
    have small : 2^n ≤ 2^62 := Nat.pow_le_pow_right (by decide) (by omega)
    have double : 2^(n+1) = 2*2^n := by rw [Nat.pow_succ]; omega
    rw [double] at width
    obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
    have c1 : ¬ stop.val ≤ loc.val := by scalar_tac
    have c2 : ¬ e.val ≤ s.val := by scalar_tac
    have c3 : ¬ w.val = 1 := by omega
    obtain ⟨lp, hlp, lpv⟩ := sub_ok p w (by scalar_tac)
    obtain ⟨rp, hrp, rpv⟩ := sub_ok p 1#u64 (by scalar_tac)
    have children : adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.children dyTerms o p w =
        RustM.ok (lp, rp) := by
      simp [adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.children, hlp, hrp]
    obtain ⟨half, hhalf, halfv⟩ := UScalar.div_spec w (y := 2#u64) (by decide)
    have halfv' : half.val = 2^n := by simp at halfv; omega
    obtain ⟨mid, hmid, midv⟩ := add_ok s half (by scalar_tac)
    have collect : ∀ (o' : Opening) a b c d,
        adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.collect dyTerms o' a b c d =
          RustM.ok o' := fun _ _ _ _ _ => rfl
    have nodeOk : ∀ (o' : Opening) (q : Std.U64) (l r : Bytes),
        adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.node dyTerms o' q l r =
          RustM.ok (node q.val l r) := fun _ q l r => node_eq q l r
    by_cases side : loc.val < s.val + 2^n
    · -- The left call holds the item; the right subtree is one sibling.
      obtain ⟨r, hr, agree⟩ := ih lp half s loc e o halfv' (by omega) (by scalar_tac)
        (by scalar_tac) low (by omega) finish hitem hsib cursor
      rw [show lp.val = p.val - 2*2^n by scalar_tac] at agree
      have right : ∀ o1 : Opening, traversal.reconstruct backend o1 rp half mid loc e =
          adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling dyTerms o1 := fun o1 => outside o1 rp half mid loc e (by scalar_tac)
            (Or.inr (by scalar_tac))
      obtain ⟨res, o1⟩ := r
      cases hm : replay item n (p.val - 2*2^n) s.val loc.val (sib.val.drop o.next.val) with
      | none =>
        cases res with
        | Ok d => simp [hm, Traversed] at agree
        | Err err =>
          refine ⟨(.Err err, o1), ?_, ?_⟩
          · rw [traversal.reconstruct.eq_def]; simp only [hstop, bind_ok]
            simp [c1, c2, c3, children, hhalf, hmid, collect, nodeOk, hr]
          · simp [replay, double, side, hm, Traversed]
      | some m =>
        obtain ⟨d', rest⟩ := m
        cases res with
        | Err err => simp [hm, Traversed] at agree
        | Ok d =>
          simp only [hm, Traversed] at agree
          obtain ⟨rfl, i1, s1, within, rfl⟩ := agree
          by_cases room : o1.next.val < sib.length
          · obtain ⟨n1, hn1, n1v⟩ := sibling_ok o1 (by rw [s1]; exact room)
            refine ⟨(.Ok (node p.val d sib.val[o1.next.val]), { o1 with next := n1 }), ?_, ?_⟩
            · rw [traversal.reconstruct.eq_def]; simp only [hstop, bind_ok]
              simp [c1, c2, c3, children, hhalf, hmid, collect, nodeOk, hr, right, hn1, s1]
            · have unfolded : replay item (n+1) p.val s.val loc.val (sib.val.drop o.next.val) =
                  some (node p.val d sib.val[o1.next.val], sib.val.drop (o1.next.val + 1)) := by
                simp only [replay, double, side, ↓reduceIte, hm, List.drop_eq_getElem_cons room]
                rfl
              rw [unfolded]
              simpa [Traversed, n1v, i1, s1] using room
          · refine ⟨(.Err .MissingDigests, o1), ?_, ?_⟩
            · rw [traversal.reconstruct.eq_def]; simp only [hstop, bind_ok]
              simp [c1, c2, c3, children, hhalf, hmid, collect, nodeOk, hr, right,
                sibling_end o1 (by rw [s1]; exact room)]
            · have unfolded : replay item (n+1) p.val s.val loc.val (sib.val.drop o.next.val) =
                  none := by
                simp only [replay, double, side, ↓reduceIte, hm,
                  List.drop_eq_nil_of_le (Nat.le_of_not_lt room)]
                rfl
              rw [unfolded]
              simp [Traversed]
    · -- The left subtree is one sibling; the right call holds the item.
      have left : traversal.reconstruct backend o lp half s loc e = adapter.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling dyTerms o :=
        outside o lp half s loc e (by scalar_tac) (Or.inl (by scalar_tac))
      by_cases room : o.next.val < sib.length
      · obtain ⟨n1, hn1, n1v⟩ := sibling_ok o (by rw [hsib]; exact room)
        obtain ⟨r, hr, agree⟩ := ih rp half mid loc e { o with next := n1 } halfv' (by omega)
          (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) finish hitem hsib
          (by simp only; omega)
        rw [show rp.val = p.val - 1 by scalar_tac, show mid.val = s.val + 2^n by scalar_tac] at agree
        simp only at agree
        rw [n1v] at agree
        obtain ⟨res, o2⟩ := r
        cases hm : replay item n (p.val - 1) (s.val + 2^n) loc.val
            (sib.val.drop (o.next.val + 1)) with
        | none =>
          cases res with
          | Ok d => simp [hm, Traversed] at agree
          | Err err =>
            refine ⟨(.Err err, o2), ?_, ?_⟩
            · rw [traversal.reconstruct.eq_def]; simp only [hstop, bind_ok]
              simp [c1, c2, c3, children, hhalf, hmid, collect, nodeOk, left, hn1, hr]
            · have unfolded : replay item (n+1) p.val s.val loc.val (sib.val.drop o.next.val) =
                  none := by
                simp only [replay, side, ↓reduceIte, List.drop_eq_getElem_cons room, hm]
                rfl
              rw [unfolded]
              simp [Traversed]
        | some m =>
          obtain ⟨d', rest⟩ := m
          cases res with
          | Err err => simp [hm, Traversed] at agree
          | Ok d =>
            simp only [hm, Traversed] at agree
            obtain ⟨rfl, i2, s2, within, rfl⟩ := agree
            refine ⟨(.Ok (node p.val sib.val[o.next.val] d), o2), ?_, ?_⟩
            · rw [traversal.reconstruct.eq_def]; simp only [hstop, bind_ok]
              simp [c1, c2, c3, children, hhalf, hmid, collect, nodeOk, left, hn1, hr]
              subst hsib
              rfl
            · have unfolded : replay item (n+1) p.val s.val loc.val (sib.val.drop o.next.val) =
                  some (node p.val sib.val[o.next.val] d, sib.val.drop o2.next.val) := by
                simp only [replay, side, ↓reduceIte, List.drop_eq_getElem_cons room, hm]
                rfl
              rw [unfolded]
              exact ⟨rfl, i2, s2, within, rfl⟩
      · refine ⟨(.Err .MissingDigests, o), ?_, ?_⟩
        · rw [traversal.reconstruct.eq_def]; simp only [hstop, bind_ok]
          simp [c1, c2, c3, children, hhalf, hmid, collect, nodeOk, left,
            sibling_end o (by rw [hsib]; exact room)]
        · have unfolded : replay item (n+1) p.val s.val loc.val (sib.val.drop o.next.val) =
              none := by
            simp only [replay, side, ↓reduceIte, List.drop_eq_nil_of_le (Nat.le_of_not_lt room)]
          rw [unfolded]
          simp [Traversed]


theorem traversal_verify_eq (h : Std.U32) (loc : Std.U64) (root : Bytes) (item : ByteArray)
    (sib : Slice Bytes) :
    adapter.verify dyTerms h loc root item sib =
      RustM.ok (Reference.check h.val loc.val root item sib.val) := by
  rw [adapter.verify]
  by_cases tall : h.val > 63
  · have : h > adapter.MAX_HEIGHT := by simp [adapter.MAX_HEIGHT]; scalar_tac
    simp [this, Reference.check]
    omega
  · have short : ¬ h > adapter.MAX_HEIGHT := by simp [adapter.MAX_HEIGHT]; scalar_tac
    obtain ⟨leaves, hl, lv⟩ := pow_ok h (by omega)
    have pos : 1 ≤ 2^h.val := Nat.one_le_two_pow
    have small : 2^h.val ≤ 2^63 := Nat.pow_le_pow_right (by decide) (by omega)
    by_cases out : loc.val ≥ 2^h.val
    · have outv : ¬ loc.val < 2^h.val := by omega
      simp [short, hl, Reference.check, outv, lv]
    · have inside : ¬ loc ≥ leaves := by scalar_tac
      obtain ⟨i, hi, iv⟩ := sub_ok leaves 1#u64 (by scalar_tac)
      obtain ⟨i1, hi1, i1v⟩ := mul_ok 2#u64 i (by scalar_tac)
      obtain ⟨stop, hstop, stopv⟩ := add_ok loc 1#u64 (by scalar_tac)
      obtain ⟨r, hr, agree⟩ := traverse_eq item sib h.val i1 leaves 0#u64 loc stop
        { item, siblings := sib, next := 0#usize } lv (by omega) (by scalar_tac)
        (by simp; omega) (by simp) (by simp; omega) (by scalar_tac) rfl rfl (by simp)
      rw [show i1.val = 2*(2^h.val-1) by scalar_tac] at agree
      have z1 : (0#u64).val = 0 := rfl
      have z2 : (0#usize).val = 0 := rfl
      simp only [z1, z2, List.drop_zero] at agree
      simp only [short, ↓reduceIte, hl, bind_ok, inside, hi, hi1, hstop, hr]
      have bounds : h.val ≤ 63 ∧ loc.val < 2^h.val := ⟨by omega, by omega⟩
      unfold Reference.check
      obtain ⟨res, o⟩ := r
      cases hm : replay item h.val (2*(2^h.val-1)) 0 loc.val sib.val with
      | none =>
        cases res with
        | Ok d => simp [hm, Traversed] at agree
        | Err err => simp [bounds]
      | some m =>
        obtain ⟨peak, rest⟩ := m
        cases res with
        | Err err => simp [hm, Traversed] at agree
        | Ok d =>
          simp only [hm, Traversed] at agree
          obtain ⟨rfl, -, s1, within, rfl⟩ := agree
          have eqv : (o.next = Slice.len sib) ↔ o.next.val = sib.length := by
            constructor
            · intro c; rw [c, Slice.len_val]
            · intro c; scalar_tac
          by_cases full : o.next.val = sib.length
          · have empty : sib.val.drop o.next.val = [] := List.drop_eq_nil_of_le (by
              simp only [Slice.length] at full; omega)
            rw [empty]
            simp [len_ok, eqv, full, wrap_eq h (by omega), eq_ok, bounds]
          · have room : o.next.val < sib.val.length := by
              simp only [Slice.length] at within full; omega
            rw [List.drop_eq_getElem_cons room]
            simp [len_ok, eqv, full, bounds]

/-! ## Binding of the production verifier -/

theorem ok_inj {α} {x y : α} (h : RustM.ok x = RustM.ok y) : x = y := by
  have := congrArg RustM.match h
  simpa using this

/-- An accepted model replay uses exactly one sibling per level. -/
theorem replay_length (item : ByteArray) : ∀ (H p s loc : Nat) (ws : List Bytes) (d : Bytes)
    (rest : List Bytes), replay item H p s loc ws = some (d, rest) →
      ws.length = H + rest.length := by
  intro H
  induction H with
  | zero =>
    intro p s loc ws d rest run
    simp [replay] at run
    obtain ⟨-, rfl⟩ := run
    simp
  | succ n ih =>
    intro p s loc ws d rest run
    simp only [replay] at run
    split at run
    · cases hr : replay item n (p - 2^(n+1)) s loc ws with
      | none => simp [hr] at run
      | some pair =>
        obtain ⟨l, r⟩ := pair
        cases r with
        | nil => simp [hr] at run
        | cons x xs =>
          simp [hr] at run
          obtain ⟨-, rfl⟩ := run
          have := ih _ _ _ _ _ _ hr
          simp at this
          omega
    · cases ws with
      | nil => simp at run
      | cons x tail =>
        cases hr : replay item n (p - 1) (s + 2^n) loc tail with
        | none => simp [hr] at run
        | some pair =>
          obtain ⟨r, rest'⟩ := pair
          simp [hr] at run
          obtain ⟨-, rfl⟩ := run
          have := ih _ _ _ _ _ _ hr
          simp
          omega

/-- Two openings that the production verifier accepts at the same location under the same root
carry the same item. -/
theorem binding (h : Std.U32) (loc : Std.U64) (root : Bytes) (a b : ByteArray)
    (wa wb : Slice Bytes) (ha : adapter.verify dyTerms h loc root a wa = RustM.ok true)
    (hb : adapter.verify dyTerms h loc root b wb = RustM.ok true) : a = b := by
  rw [traversal_verify_eq] at ha hb
  exact fixed_root_binding _ _ _ _ _ _ _ ((Reference.check_spec ..).mp (ok_inj ha))
    ((Reference.check_spec ..).mp (ok_inj hb))

/-- The honest tree's root satisfies the snapshot assumption: every stored item has an opening
that the production verifier accepts. -/
theorem honest_opening_accepted (items : Nat → ByteArray) (h : Std.U32) (bound : h.val ≤ 63)
    (loc : Std.U64) (inside : loc.val < 2^h.val) :
    ∃ ws : Slice Bytes, adapter.verify dyTerms h loc
      (wrap h.val (tree items h.val (2*(2^h.val-1)) 0)) (items loc.val) ws = RustM.ok true := by
  obtain ⟨ws, valid⟩ := honest_opening items h.val loc.val bound inside
  obtain ⟨-, -, peak, run, -⟩ := id valid
  have length := replay_length _ _ _ _ _ _ _ _ run
  simp at length
  refine ⟨Slice.from ws (by scalar_tac), ?_⟩
  rw [traversal_verify_eq, Slice.from_val]
  congr 1
  exact (Reference.check_spec ..).mpr valid

/-! ## The client -/

/-- Every event that the reference decision accepts names the snapshot height, an in-range
location and the stored item. -/
theorem step_sound [Snapshot] (message : Bytes) (loc : Std.U64) (ws : Slice Bytes)
    (event : Reference.Acceptance) (accepted : Reference.step message loc ws = some event) :
    event.height = Snapshot.height ∧ event.location.val < 2^event.height.val ∧
      event.item = Snapshot.items event.location.val := by
  unfold Reference.step at accepted
  split at accepted
  · simp at accepted
  · split at accepted
    · rename_i checked
      cases accepted
      have valid := (Reference.check_spec ..).mp checked
      obtain ⟨ws', honest⟩ := Snapshot.honest loc valid.2.1
      rw [traversal_verify_eq] at honest
      have stored := (Reference.check_spec ..).mp (ok_inj honest)
      exact ⟨rfl, valid.2.1, fixed_root_binding _ _ _ _ _ _ _ valid stored⟩
    · simp at accepted

theorem client_step_eq [Snapshot] (message : Bytes) (loc : Std.U64) (ws : Slice Bytes) :
    client.client_step dyTerms Snapshot.root Snapshot.height message loc ws =
      RustM.ok (match Reference.step message loc ws with
        | some event => core.option.Option.Some event
        | none => core.option.Option.None) := by
  have parse : dyTerms.parse message = RustM.ok (match Literal.bytesToLiteral message with
      | some x => core.option.Option.Some x
      | none => core.option.Option.None) := rfl
  unfold client.client_step Reference.step
  simp only [parse, bind_ok]
  cases Literal.bytesToLiteral message with
  | none => rfl
  | some item =>
    simp only [traversal_verify_eq, bind_ok]
    cases Reference.check (Snapshot.height).val loc.val Snapshot.root item ws.val <;> rfl

#print axioms traverse_eq
#print axioms traversal_verify_eq
#print axioms binding
#print axioms honest_opening_accepted
#print axioms step_sound
#print axioms client_step_eq
end
end Qmdb.Correspondence
