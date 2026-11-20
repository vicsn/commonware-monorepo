module
public import Hashing

/-! The extracted production verifier under an arbitrary hash. Position binding: two openings that
it accepts at the same location under the same root carry the same item, or `finder` returns two
different hash inputs with the same digest. It also returns a verdict on every input and accepts
every honest opening. Checked by Lean; only the statements used by `Symbolic`, `Protocol` and
`SecurityTheorems` matter for review. -/

namespace Qmdb.Verifier
open Aeneas Aeneas.Std Aeneas.Std.WP CoreModels qmdb_dylean
@[expose] public section

variable {D M : Type} [DecidableEq D]

/-! ## Machine arithmetic and monadic plumbing -/

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

/-! ## Hash inputs -/

/-- The big-endian bytes of a 64-bit integer. -/
def be (x : Std.U64) : Slice Std.U8 :=
  (Aeneas.Std.core.num.U64.to_be_bytes x).to_slice

/-- The hash input of the leaf at position `p` holding `item`. -/
def leafInput (S : Scheme D M) (p : Std.U64) (item : Slice Std.U8) : M :=
  S.encode [.Bytes (be p), .Bytes item]

/-- The hash input of the node at position `p` with the given child digests. -/
def nodeInput (S : Scheme D M) (p : Std.U64) (left right : D) : M :=
  S.encode [.Bytes (be p), .Digest left, .Digest right]

/-- The hash input of the root over one peak. -/
def rootInput (S : Scheme D M) (domain : Aeneas.Std.Array Std.U8 2#usize) (leaves : Std.U64)
    (peak : D) : M :=
  S.encode [.Bytes domain.to_slice, .Bytes (be leaves), .Digest peak]

theorem to_be_bytes_ok (x : Std.U64) :
    CoreModels.core.num.U64.to_be_bytes x = RustM.ok (Aeneas.Std.core.num.U64.to_be_bytes x) := by
  simp [CoreModels.core.num.U64.to_be_bytes, rust_primitives.arithmetic.to_be_bytes_u64]

theorem leaf_eq (S : Scheme D M) (u : Unit) (p : Std.U64) (item : Slice Std.U8) :
    terms.leaf_digest S.terms u p item = RustM.ok (S.hash (leafInput S p item)) := by
  simp [terms.leaf_digest, to_be_bytes_ok, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, Scheme.terms, leafInput, be]

theorem node_eq (S : Scheme D M) (u : Unit) (p : Std.U64) (left right : D) :
    terms.node_digest S.terms u p left right = RustM.ok (S.hash (nodeInput S p left right)) := by
  simp [terms.node_digest, to_be_bytes_ok, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, Scheme.terms, nodeInput, be]

theorem root_eq (S : Scheme D M) (u : Unit) (domain : Aeneas.Std.Array Std.U8 2#usize)
    (leaves : Std.U64) (peak : D) :
    terms.root S.terms u domain leaves 0#u64 peak =
      RustM.ok (S.hash (rootInput S domain leaves peak)) := by
  simp [terms.root, to_be_bytes_ok, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, Scheme.terms, rootInput, be]

/-! ## The production backend -/

abbrev Opening (D : Type) := traversal.Opening (client.Mmr Unit) client.Single Unit D
abbrev mmr (S : Scheme D M) := client.Mmr.Insts.Qmdb_dyleanTraversalNodes S.terms
abbrev single := client.Single.Insts.CoreIterTraitsIteratorIteratorElement
abbrev element := client.Element.Insts.CoreConvertAsRefSliceU8
abbrev noCollect (D : Type) := Tuple.Insts.Qmdb_dyleanTraversalCollect D
abbrev backend (S : Scheme D M) :=
  traversal.Opening.Insts.Qmdb_dyleanTraversalBackend (mmr S) single element (noCollect D)

theorem index_ok {α} (s : Slice α) (i : Std.Usize) (bound : i.val < s.length) :
    Slice.index_usize s i = RustM.ok s.val[i.val] := by
  obtain ⟨x, hx, _, rfl⟩ := ok_of_partialSpec (Slice.index_usize_spec s i)
    (by intro e; cases e <;> simp; omega) (by simp)
  exact hx

theorem sibling_ok (S : Scheme D M) (o : Opening D) (room : o.cursor.val < o.siblings.length) :
    ∃ c : Std.Usize, traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling (mmr S) single
      element (noCollect D) o =
        RustM.ok (.Ok o.siblings.val[o.cursor.val], { o with cursor := c }) ∧
      c.val = o.cursor.val + 1 := by
  obtain ⟨c, hc, cv⟩ := succ_ok o.cursor o.siblings room
  refine ⟨c, ?_, cv⟩
  have roomv : o.cursor.val < o.siblings.val.length := room
  simp [traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling,
    CoreModels.core.slice.Slice.get, roomv,
    CoreModels.core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    rust_primitives.slice.slice_length,
    rust_primitives.slice.slice_index, index_ok o.siblings o.cursor room, hc]

theorem sibling_end (S : Scheme D M) (o : Opening D)
    (none_left : ¬ o.cursor.val < o.siblings.length) :
    traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling (mmr S) single element
      (noCollect D) o = RustM.ok (.Err .MissingDigests, o) := by
  have endv : ¬ o.cursor.val < o.siblings.val.length := none_left
  simp [traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling,
    CoreModels.core.slice.Slice.get, endv,
    CoreModels.core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    rust_primitives.slice.slice_length]

/-- A sibling read that succeeds returns the next unread sibling and keeps the element source. -/
theorem sibling_read (S : Scheme D M) (o x : Opening D) (d : D)
    (h : traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling (mmr S) single element
      (noCollect D) o = RustM.ok (.Ok d, x)) :
    o.siblings.val.drop o.cursor.val = d :: x.siblings.val.drop x.cursor.val ∧
      x.siblings = o.siblings ∧ x.elements = o.elements := by
  by_cases room : o.cursor.val < o.siblings.length
  · obtain ⟨c, hc, cv⟩ := sibling_ok S o room
    rw [hc] at h
    have same := ok_inj h
    simp only [Prod.mk.injEq, CoreModels.core.result.Result.Ok.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    refine ⟨?_, rfl, rfl⟩
    have roomv : o.cursor.val < o.siblings.val.length := room
    simp only [cv]
    exact List.drop_eq_getElem_cons roomv
  · rw [sibling_end S o room] at h
    have same := ok_inj h
    simp at same

theorem leaf_some (S : Scheme D M) (o : Opening D) (a : Slice Std.U8) (h : o.elements = some a)
    (p : Std.U64) :
    traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.leaf (mmr S) single element (noCollect D)
      o p = RustM.ok (.Ok (S.hash (leafInput S p a)), { o with elements := none }) := by
  simp [traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.leaf, h,
    client.Single.Insts.CoreIterTraitsIteratorIteratorElement.next,
    client.Element.Insts.CoreConvertAsRefSliceU8.as_ref,
    client.Mmr.Insts.Qmdb_dyleanTraversalNodes.leaf_digest, leaf_eq]

theorem ilog2_ok (w : Std.U64) (n : Nat) (hw : w.val = 2^n) :
    CoreModels.core.num.U64.ilog2 w = RustM.ok (⟨BitVec.ofNat 32 n⟩ : Std.U32) := by
  simp [CoreModels.core.num.U64.ilog2, rust_primitives.arithmetic.ilog2_u64, uilog2, hw,
    Nat.log2_two_pow]

theorem children_ok (S : Scheme D M) (p w : Std.U64) (n : Nat) (hw : w.val = 2^n) (hn : n ≤ 62)
    (hp : w.val ≤ p.val) (one : 1 ≤ p.val) :
    ∃ lp rp : Std.U64, (∀ o : Opening D,
      traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.children (mmr S) single element
        (noCollect D) o p w = RustM.ok (lp, rp)) ∧ lp.val = p.val - w.val ∧
      rp.val = p.val - 1 := by
  have height : (⟨BitVec.ofNat 32 n⟩ : Std.U32).val = n := by
    change (BitVec.ofNat 32 n).toNat = n
    simp
    omega
  obtain ⟨z, hz, zv⟩ := pow_ok ⟨BitVec.ofNat 32 n⟩ (by omega)
  rw [height] at zv
  obtain ⟨lp, hlp, lpv⟩ := sub_ok p z (by omega)
  obtain ⟨rp, hrp, rpv⟩ := sub_ok p 1#u64 (by scalar_tac)
  refine ⟨lp, rp, fun o => ?_, by omega, by simpa using rpv⟩
  simp [traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.children, ilog2_ok w n hw,
    client.Mmr.Insts.Qmdb_dyleanTraversalNodes.children, hz, hlp, hrp]

theorem collect_ok (S : Scheme D M) (o : Opening D) (lp : Std.U64) (l : D) (rp : Std.U64)
    (r : D) :
    traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.collect (mmr S) single element
      (noCollect D) o lp l rp r = RustM.ok o := by
  simp [traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.collect,
    Tuple.Insts.Qmdb_dyleanTraversalCollect.collect]

theorem node_ok (S : Scheme D M) (o : Opening D) (p : Std.U64) (l r : D) :
    traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.node (mmr S) single element (noCollect D)
      o p l r = RustM.ok (S.hash (nodeInput S p l r)) := by
  simp [traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.node,
    client.Mmr.Insts.Qmdb_dyleanTraversalNodes.node_digest, node_eq]

/-- A subtree outside the queried range is read as one sibling. -/
theorem outside (S : Scheme D M) (o : Opening D) (p w s loc e : Std.U64)
    (bound : s.val + w.val ≤ 2^62) (off : s.val + w.val ≤ loc.val ∨ e.val ≤ s.val) :
    traversal.reconstruct (backend S) o p w s loc e =
      traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling (mmr S) single element
        (noCollect D) o := by
  obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
  rw [traversal.reconstruct.eq_def]
  simp only [hstop, bind_ok]
  by_cases before : s.val + w.val ≤ loc.val
  · have : stop.val ≤ loc.val := by omega
    simp [this]
  · have after : e.val ≤ s.val := by omega
    have : ¬ stop.val ≤ loc.val := by omega
    simp [this, after]

/-- A subtree of one leaf inside the queried range is read as that leaf. -/
theorem reconstruct_one (S : Scheme D M) (o : Opening D) (p w s loc e : Std.U64)
    (hw : w.val = 1) (bound : s.val + 1 ≤ 2^62) (c1 : ¬ s.val + 1 ≤ loc.val)
    (c2 : ¬ e.val ≤ s.val) :
    traversal.reconstruct (backend S) o p w s loc e =
      traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.leaf (mmr S) single element
        (noCollect D) o p := by
  obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
  have c1' : ¬ stop.val ≤ loc.val := by omega
  have c3 : w = 1#u64 := by scalar_tac
  rw [traversal.reconstruct.eq_def]
  simp only [hstop, bind_ok]
  simp [c1', c2, c3]

theorem reconstruct_leaf (S : Scheme D M) (o : Opening D) (a : Slice Std.U8)
    (h : o.elements = some a) (p w s loc e : Std.U64) (hw : w.val = 1) (bound : s.val + 1 ≤ 2^62)
    (inside : s.val ≤ loc.val ∧ loc.val < s.val + 1) (finish : e.val = loc.val + 1) :
    traversal.reconstruct (backend S) o p w s loc e =
      RustM.ok (.Ok (S.hash (leafInput S p a)), { o with elements := none }) := by
  rw [reconstruct_one S o p w s loc e hw bound (by omega) (by omega), leaf_some S o a h p]

/-! ## The hash inputs of an opening -/

/-- The 64-bit integer with value `x`, for `x < 2^64`. -/
def pos (x : Nat) : Std.U64 := ⟨BitVec.ofNat 64 x⟩

theorem pos_val (x : Std.U64) : pos x.val = x := by
  apply UScalar.eq_of_val_eq
  change (BitVec.ofNat 64 x.val).toNat = x.val
  have : x.val < 2^64 := by scalar_tac
  simp

/-- The hash inputs on the path of an opening through the height-`n` subtree at position `p` with
first leaf `s`, for `item` at leaf `loc` and the siblings `ws`: the subtree's own input, the
inputs below it down to the leaf's, and the siblings left unread. The subtree's digest is the
hash of its own input. -/
def inputs (S : Scheme D M) (item : Slice Std.U8) (loc : Nat) :
    Nat → Nat → Nat → List D → Option (M × List M × List D)
  | 0, p, _, ws => some (leafInput S (pos p) item, [], ws)
  | n+1, p, s, ws =>
    if loc < s + 2^n then
      match inputs S item loc n (p - 2^(n+1)) s ws with
      | some (m, ms, r :: rest) => some (nodeInput S (pos p) (S.hash m) r, m :: ms, rest)
      | _ => none
    else
      match ws with
      | l :: ws =>
        match inputs S item loc n (p - 1) (s + 2^n) ws with
        | some (m, ms, rest) => some (nodeInput S (pos p) l (S.hash m), m :: ms, rest)
        | none => none
      | [] => none

omit [DecidableEq D] in
theorem inputs_left {S : Scheme D M} {item : Slice Std.U8} {loc n p s : Nat} {ws rest : List D}
    {m : M} {ms : List M} (side : loc < s + 2^n)
    (h : inputs S item loc (n+1) p s ws = some (m, ms, rest)) :
    ∃ m' ms' r, inputs S item loc n (p - 2^(n+1)) s ws = some (m', ms', r :: rest) ∧
      m = nodeInput S (pos p) (S.hash m') r ∧ ms = m' :: ms' := by
  rw [inputs.eq_def] at h
  simp only [side, ↓reduceIte] at h
  cases below : inputs S item loc n (p - 2^(n+1)) s ws with
  | none => simp [below] at h
  | some found =>
    obtain ⟨m', ms', unread⟩ := found
    cases unread with
    | nil => simp [below] at h
    | cons r rest' =>
      simp only [below, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨m', ms', r, rfl, rfl, rfl⟩

omit [DecidableEq D] in
theorem inputs_right {S : Scheme D M} {item : Slice Std.U8} {loc n p s : Nat} {ws rest : List D}
    {m : M} {ms : List M} (side : ¬ loc < s + 2^n)
    (h : inputs S item loc (n+1) p s ws = some (m, ms, rest)) :
    ∃ l ws' m' ms', ws = l :: ws' ∧ inputs S item loc n (p - 1) (s + 2^n) ws' =
      some (m', ms', rest) ∧ m = nodeInput S (pos p) l (S.hash m') ∧ ms = m' :: ms' := by
  rw [inputs.eq_def] at h
  simp only [side, ↓reduceIte] at h
  cases ws with
  | nil => simp at h
  | cons l ws' =>
    cases below : inputs S item loc n (p - 1) (s + 2^n) ws' with
    | none => simp [below] at h
    | some found =>
      obtain ⟨m', ms', unread⟩ := found
      simp only [below, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨l, ws', m', ms', rfl, below, rfl, rfl⟩

/-- A successful run of the production traversal over a subtree that holds the queried location
hashes exactly the inputs of `inputs` and returns the hash of the first. -/
theorem reconstruct_inputs (S : Scheme D M) (H : Nat) : ∀ (p w s loc e : Std.U64)
    (o r : Opening D) (item : Slice Std.U8) (d : D), w.val = 2^H → H ≤ 62 →
    2*(w.val-1) ≤ p.val → s.val + w.val ≤ 2^62 → s.val ≤ loc.val → loc.val < s.val + w.val →
    e.val = loc.val + 1 → o.elements = some item →
    traversal.reconstruct (backend S) o p w s loc e = RustM.ok (.Ok d, r) →
    ∃ m ms, inputs S item loc.val H p.val s.val (o.siblings.val.drop o.cursor.val) =
      some (m, ms, r.siblings.val.drop r.cursor.val) ∧ S.hash m = d ∧
      r.siblings = o.siblings := by
  induction H with
  | zero =>
    intro p w s loc e o r item d width _ _ bound low high finish elems run
    simp at width
    rw [reconstruct_leaf S o item elems p w s loc e width (by omega) ⟨low, by omega⟩ finish]
      at run
    have same := ok_inj run
    simp only [Prod.mk.injEq, CoreModels.core.result.Result.Ok.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨_, [], by simp [inputs, pos_val], rfl, rfl⟩
  | succ n ih =>
    intro p w s loc e o r item d width bound position start low high finish elems run
    have one : 1 ≤ 2^n := Nat.one_le_two_pow
    have small : 2^n ≤ 2^61 := Nat.pow_le_pow_right (by decide) (by omega)
    have double : 2^(n+1) = 2*2^n := by rw [Nat.pow_succ]; omega
    obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
    have c1 : ¬ stop.val ≤ loc.val := by omega
    have c2 : ¬ e.val ≤ s.val := by omega
    have c3 : ¬ w.val = 1 := by omega
    obtain ⟨lp, rp, kids, lpv, rpv⟩ := children_ok S p w (n+1) width bound (by omega) (by omega)
    obtain ⟨half, hhalf, halfv⟩ := UScalar.div_spec w (y := 2#u64) (by decide)
    have halfv' : half.val = 2^n := by simp at halfv; omega
    obtain ⟨mid, hmid, midv⟩ := add_ok s half (by scalar_tac)
    have lpn : p.val - 2^(n+1) = lp.val := by omega
    have rpn : p.val - 1 = rp.val := by omega
    have midn : s.val + 2^n = mid.val := by omega
    rw [traversal.reconstruct.eq_def] at run
    simp only [hstop, bind_ok] at run
    simp [c1, c2, c3, kids, hhalf, hmid] at run
    obtain ⟨⟨res, x⟩, hl, k⟩ := bind_eq_ok run
    cases res with
    | Err _ => simp at k
    | Ok l =>
      obtain ⟨⟨res', y⟩, hr, k'⟩ := bind_eq_ok k
      cases res' with
      | Err _ => simp at k'
      | Ok rr =>
        simp [collect_ok, node_ok] at k'
        obtain ⟨rfl, rfl⟩ := k'
        by_cases side : loc.val < mid.val
        · obtain ⟨m, ms, below, rfl, xs⟩ := ih lp half s loc e o x item l halfv' (by omega)
            (by omega) (by omega) low (by omega) finish elems hl
          rw [outside S x rp half mid loc e (by omega) (Or.inr (by omega))] at hr
          obtain ⟨unread, ys, -⟩ := sibling_read S x y rr hr
          rw [unread] at below
          refine ⟨_, m :: ms, ?_, rfl, ys.trans xs⟩
          rw [inputs.eq_def]
          simp only [midn, side, ↓reduceIte, lpn, below, pos_val]
        · rw [outside S o lp half s loc e (by omega) (Or.inl (by omega))] at hl
          obtain ⟨unread, xs, xe⟩ := sibling_read S o x l hl
          obtain ⟨m, ms, below, rfl, ys⟩ := ih rp half mid loc e x y item rr halfv' (by omega)
            (by omega) (by omega) (by omega) (by omega) finish (xe.trans elems) hr
          refine ⟨_, m :: ms, ?_, rfl, ys.trans xs⟩
          rw [inputs.eq_def]
          simp only [midn, side, ↓reduceIte, unread, rpn, below, pos_val]

/-! ## Collision finder -/

theorem head_mem_zip {α β} (x : α) (xs : List α) (y : β) (ys : List β) :
    (x, y) ∈ (x :: xs).zip (y :: ys) := by
  simp

theorem tail_mem_zip {α β} {c : α × β} (x : α) {xs : List α} (y : β) {ys : List β}
    (h : c ∈ xs.zip ys) : c ∈ (x :: xs).zip (y :: ys) := by
  simp [h]

omit [DecidableEq D] in
/-- Corresponding hash inputs of two openings whose roots agree: the same item, or two inputs
that differ and have the same digest. -/
theorem inputs_clash (S : Scheme D M) (enc : S.Unambiguous) (a b : Slice Std.U8) (loc : Nat)
    (n : Nat) : ∀ (p s : Nat) (wa wb : List D) (m₁ : M) (ms₁ : List M) (r₁ : List D) (m₂ : M)
    (ms₂ : List M) (r₂ : List D), inputs S a loc n p s wa = some (m₁, ms₁, r₁) →
    inputs S b loc n p s wb = some (m₂, ms₂, r₂) → S.hash m₁ = S.hash m₂ →
    a = b ∨ ∃ c ∈ (m₁ :: ms₁).zip (m₂ :: ms₂), S.Collision c.1 c.2 := by
  induction n with
  | zero =>
    intro p s wa wb m₁ ms₁ r₁ m₂ ms₂ r₂ h₁ h₂ digest
    simp only [inputs, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₂
    by_cases same : leafInput S (pos p) a = leafInput S (pos p) b
    · exact Or.inl (enc.leaf _ _ _ same)
    · exact Or.inr ⟨_, head_mem_zip _ _ _ _, same, digest⟩
  | succ n ih =>
    intro p s wa wb m₁ ms₁ r₁ m₂ ms₂ r₂ h₁ h₂ digest
    by_cases side : loc < s + 2^n
    · obtain ⟨m₁', ms₁', x₁, below₁, rfl, rfl⟩ := inputs_left side h₁
      obtain ⟨m₂', ms₂', x₂, below₂, rfl, rfl⟩ := inputs_left side h₂
      by_cases same : nodeInput S (pos p) (S.hash m₁') x₁ = nodeInput S (pos p) (S.hash m₂') x₂
      · rcases ih _ _ _ _ _ _ _ _ _ _ below₁ below₂ (enc.node _ _ _ _ _ same).1 with
          eq | ⟨c, mem, hc⟩
        · exact Or.inl eq
        · exact Or.inr ⟨c, tail_mem_zip _ _ mem, hc⟩
      · exact Or.inr ⟨_, head_mem_zip _ _ _ _, same, digest⟩
    · obtain ⟨l₁, wa', m₁', ms₁', rfl, below₁, rfl, rfl⟩ := inputs_right side h₁
      obtain ⟨l₂, wb', m₂', ms₂', rfl, below₂, rfl, rfl⟩ := inputs_right side h₂
      by_cases same : nodeInput S (pos p) l₁ (S.hash m₁') = nodeInput S (pos p) l₂ (S.hash m₂')
      · rcases ih _ _ _ _ _ _ _ _ _ _ below₁ below₂ (enc.node _ _ _ _ _ same).2 with
          eq | ⟨c, mem, hc⟩
        · exact Or.inl eq
        · exact Or.inr ⟨c, tail_mem_zip _ _ mem, hc⟩
      · exact Or.inr ⟨_, head_mem_zip _ _ _ _, same, digest⟩

abbrev domain : Aeneas.Std.Array Std.U8 2#usize :=
  Array.make 2#usize [client.MMR_DOMAIN, client.FORWARD_FOLD]

/-- The hash inputs that `verify` builds for an opening, the root's first and the leaf's last. -/
def openingInputs (S : Scheme D M) (h : Std.U32) (loc : Std.U64) (item : Slice Std.U8)
    (ws : Slice D) : Option (List M) :=
  match inputs S item loc.val h.val (2*(2^h.val-1)) 0 ws.val with
  | some (m, ms, _) => some (rootInput S domain (pos (2^h.val)) (S.hash m) :: m :: ms)
  | none => none

/-- The first pair of corresponding hash inputs of two openings that differ and have the same
digest. -/
def finder (S : Scheme D M) [DecidableEq M] (h : Std.U32) (loc : Std.U64) (a b : Slice Std.U8)
    (wa wb : Slice D) : Option (M × M) :=
  match openingInputs S h loc a wa, openingInputs S h loc b wb with
  | some xs, some ys => (xs.zip ys).find? fun c => decide (c.1 ≠ c.2 ∧ S.hash c.1 = S.hash c.2)
  | _, _ => none

theorem find_clash (S : Scheme D M) [DecidableEq M] (l : List (M × M))
    (h : ∃ c ∈ l, S.Collision c.1 c.2) :
    ∃ x y, l.find? (fun c => decide (c.1 ≠ c.2 ∧ S.hash c.1 = S.hash c.2)) = some (x, y) ∧
      S.Collision x y := by
  obtain ⟨c, mem, hc⟩ := h
  cases found : l.find? (fun c => decide (c.1 ≠ c.2 ∧ S.hash c.1 = S.hash c.2)) with
  | none =>
    have := List.find?_eq_none.mp found c mem
    exact absurd hc (by simpa [Scheme.Collision] using this)
  | some d =>
    have := List.find?_some found
    exact ⟨d.1, d.2, rfl, by simpa [Scheme.Collision] using this⟩

/-! ## The verifier -/

theorem eq_ok (S : Scheme D M) (a b : D) :
    S.terms.corecmpPartialEqInst.eq a b = RustM.ok (decide (a = b)) :=
  rfl

/-- What an accepting `verify` has checked. -/
theorem verify_true (S : Scheme D M) {h : Std.U32} {loc : Std.U64} {root : D}
    {item : Slice Std.U8} {ws : Slice D}
    (acc : client.verify S.terms () h loc root item ws = RustM.ok true) :
    h.val ≤ 62 ∧ loc.val < 2^h.val ∧ ∃ (w p e : Std.U64) (peak : D) (r : Opening D),
      w.val = 2^h.val ∧ p.val = 2*(2^h.val-1) ∧ e.val = loc.val + 1 ∧
      traversal.reconstruct (backend S)
        { nodes := (), elements := some item, siblings := ws, cursor := 0#usize, collected := () }
        p w 0#u64 loc e = RustM.ok (.Ok peak, r) ∧ S.hash (rootInput S domain w peak) = root := by
  unfold client.verify at acc
  by_cases tall : h.val > 62
  · have : h > client.MAX_HEIGHT := by simp [client.MAX_HEIGHT]; scalar_tac
    simp [this] at acc
  · have short : ¬ h > client.MAX_HEIGHT := by simp [client.MAX_HEIGHT]; scalar_tac
    have small : 2^h.val ≤ 2^62 := Nat.pow_le_pow_right (by decide) (by omega)
    have one : 1 ≤ 2^h.val := Nat.one_le_two_pow
    obtain ⟨w, hw, wv⟩ := pow_ok h (by omega)
    by_cases out : loc.val ≥ 2^h.val
    · have : w.val ≤ loc.val := by omega
      simp [short, hw, this] at acc
    · have inside : ¬ loc ≥ w := by scalar_tac
      obtain ⟨i, hi, iv⟩ := sub_ok w 1#u64 (by scalar_tac)
      obtain ⟨p, hp, pv⟩ := mul_ok 2#u64 i (by scalar_tac)
      obtain ⟨e, he, ev⟩ := add_ok loc 1#u64 (by scalar_tac)
      simp only [short, ↓reduceIte, hw, bind_ok, inside, hi, hp, he, traversal.Opening.new] at acc
      obtain ⟨⟨res, r⟩, hrun, k⟩ := bind_eq_ok acc
      cases res with
      | Err _ => simp at k
      | Ok peak =>
        simp [traversal.Opening.impl.cursor, len_ok, root_eq, eq_ok] at k
        split at k
        · have matched := ok_inj k
          simp at matched
          exact ⟨by omega, by omega, w, p, e, peak, r, wv, by scalar_tac, by scalar_tac, hrun,
            matched⟩
        · simp at k

/-- An accepting `verify` has hashed the inputs of `inputs` up to its root. -/
theorem verify_inputs (S : Scheme D M) {h : Std.U32} {loc : Std.U64} {root : D}
    {item : Slice Std.U8} {ws : Slice D}
    (acc : client.verify S.terms () h loc root item ws = RustM.ok true) :
    h.val ≤ 62 ∧ loc.val < 2^h.val ∧ ∃ m ms rest,
      inputs S item loc.val h.val (2*(2^h.val-1)) 0 ws.val = some (m, ms, rest) ∧
      S.hash (rootInput S domain (pos (2^h.val)) (S.hash m)) = root := by
  obtain ⟨hh, hl, w, p, e, peak, r, wv, pv, ev, run, rooted⟩ := verify_true S acc
  have small : 2^h.val ≤ 2^62 := Nat.pow_le_pow_right (by decide) hh
  obtain ⟨m, ms, path, rfl, -⟩ := reconstruct_inputs S h.val p w 0#u64 loc e _ r item peak wv hh
    (by omega) (by simp; omega) (by simp) (by simp; omega) ev rfl run
  have width : w = pos (2^h.val) := by rw [← wv, pos_val]
  refine ⟨hh, hl, m, ms, r.siblings.val.drop r.cursor.val, ?_, width ▸ rooted⟩
  simpa [pv] using path

/-- Position binding of the production verifier under any hash: two openings that it accepts at
the same location under the same root carry the same item, or `finder` returns two different
hash inputs with the same digest. -/
theorem binding_or_collision (S : Scheme D M) [DecidableEq M] (enc : S.Unambiguous)
    (h : Std.U32) (loc : Std.U64) (root : D) (a b : Slice Std.U8) (wa wb : Slice D)
    (ha : client.verify S.terms () h loc root a wa = RustM.ok true)
    (hb : client.verify S.terms () h loc root b wb = RustM.ok true) :
    a = b ∨ ∃ x y, finder S h loc a b wa wb = some (x, y) ∧ S.Collision x y := by
  obtain ⟨-, -, m₁, ms₁, r₁, path₁, root₁⟩ := verify_inputs S ha
  obtain ⟨-, -, m₂, ms₂, r₂, path₂, root₂⟩ := verify_inputs S hb
  have clash : a = b ∨ ∃ c ∈ (rootInput S domain (pos (2^h.val)) (S.hash m₁) :: m₁ :: ms₁).zip
      (rootInput S domain (pos (2^h.val)) (S.hash m₂) :: m₂ :: ms₂), S.Collision c.1 c.2 := by
    by_cases same : rootInput S domain (pos (2^h.val)) (S.hash m₁) =
        rootInput S domain (pos (2^h.val)) (S.hash m₂)
    · rcases inputs_clash S enc a b loc.val h.val _ _ _ _ _ _ _ _ _ _ path₁ path₂
        (enc.root _ _ _ _ same) with eq | ⟨c, mem, hc⟩
      · exact Or.inl eq
      · exact Or.inr ⟨c, tail_mem_zip _ _ mem, hc⟩
    · exact Or.inr ⟨_, head_mem_zip _ _ _ _, same, root₁.trans root₂.symm⟩
  rcases clash with eq | found
  · exact Or.inl eq
  · right
    simpa [finder, openingInputs, path₁, path₂] using find_clash S _ found

/-! ## Honest openings -/

/-- The honest digest of the height-`n` subtree at position `p` whose first leaf is `s`. -/
def tree (S : Scheme D M) (items : Std.U64 → Slice Std.U8) : Nat → Nat → Nat → D
  | 0, p, s => S.hash (leafInput S (pos p) (items (pos s)))
  | n+1, p, s =>
    S.hash (nodeInput S (pos p) (tree S items n (p - 2^(n+1)) s)
      (tree S items n (p - 1) (s + 2^n)))

/-- The honest siblings of leaf `loc` in that subtree, in the order the traversal reads them. -/
def path (S : Scheme D M) (items : Std.U64 → Slice Std.U8) : Nat → Nat → Nat → Nat → List D
  | 0, _, _, _ => []
  | n+1, p, s, loc =>
    if loc < s + 2^n then path S items n (p - 2^(n+1)) s loc ++ [tree S items n (p - 1) (s + 2^n)]
    else tree S items n (p - 2^(n+1)) s :: path S items n (p - 1) (s + 2^n) loc

omit [DecidableEq D] in
theorem path_length (S : Scheme D M) (items : Std.U64 → Slice Std.U8) (n : Nat) :
    ∀ p s loc, (path S items n p s loc).length = n := by
  induction n with
  | zero => intros; rfl
  | succ n ih => intro p s loc; unfold path; split <;> simp [ih]

theorem drop_cons {α} {l : List α} {c : Nat} {x : α} {t : List α} (h : l.drop c = x :: t) :
    ∃ hc : c < l.length, l[c] = x ∧ l.drop (c+1) = t := by
  have first : l[c]? = some x := by
    have := congrArg (·[0]?) h
    simpa using this
  obtain ⟨hc, hx⟩ := List.getElem?_eq_some_iff.mp first
  refine ⟨hc, hx, ?_⟩
  rw [← List.tail_drop, h]
  rfl

theorem drop_append {α} {l : List α} {c : Nat} {a b : List α} (h : l.drop c = a ++ b) :
    l.drop (c + a.length) = b := by
  rw [← List.drop_drop, h, List.drop_left]

/-- The production traversal rebuilds the honest subtree digest from the honest siblings,
reading exactly them and the one claimed item. -/
theorem honest_rec (S : Scheme D M) (items : Std.U64 → Slice Std.U8) (H : Nat) :
    ∀ (p w s loc e : Std.U64) (o : Opening D) (rest : List D), w.val = 2^H → H ≤ 62 →
    2*(w.val-1) ≤ p.val → s.val + w.val ≤ 2^62 → s.val ≤ loc.val → loc.val < s.val + w.val → e.val = loc.val + 1 →
    o.elements = some (items loc) →
    o.siblings.val.drop o.cursor.val = path S items H p.val s.val loc.val ++ rest →
    ∃ r : Opening D, traversal.reconstruct (backend S) o p w s loc e =
      RustM.ok (.Ok (tree S items H p.val s.val), r) ∧ r.elements = none ∧
      r.siblings = o.siblings ∧ r.cursor.val = o.cursor.val + H := by
  induction H with
  | zero =>
    intro p w s loc e o rest width _ _ bound low high finish elems _
    simp at width
    have at_loc : s = loc := UScalar.eq_of_val_eq (by omega)
    subst at_loc
    refine ⟨{ o with elements := none }, ?_, rfl, rfl, rfl⟩
    rw [reconstruct_leaf S o (items s) elems p w s s e width (by omega) ⟨low, by omega⟩ finish]
    simp [tree, pos_val]
  | succ n ih =>
    intro p w s loc e o rest width bound position start low high finish elems sib
    have one : 1 ≤ 2^n := Nat.one_le_two_pow
    have small : 2^n ≤ 2^61 := Nat.pow_le_pow_right (by decide) (by omega)
    have double : 2^(n+1) = 2*2^n := by rw [Nat.pow_succ]; omega
    obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
    have c1 : ¬ stop.val ≤ loc.val := by omega
    have c2 : ¬ e.val ≤ s.val := by omega
    have c3 : ¬ w.val = 1 := by omega
    obtain ⟨lp, rp, kids, lpv, rpv⟩ := children_ok S p w (n+1) width bound (by omega) (by omega)
    obtain ⟨half, hhalf, halfv⟩ := UScalar.div_spec w (y := 2#u64) (by decide)
    have halfv' : half.val = 2^n := by simp at halfv; omega
    obtain ⟨mid, hmid, midv⟩ := add_ok s half (by scalar_tac)
    have lpn : p.val - 2^(n+1) = lp.val := by omega
    have rpn : p.val - 1 = rp.val := by omega
    have midn : s.val + 2^n = mid.val := by omega
    have whole : tree S items (n+1) p.val s.val =
        S.hash (nodeInput S p (tree S items n lp.val s.val) (tree S items n rp.val mid.val)) := by
      rw [tree, lpn, rpn, midn, pos_val]
    rw [whole]
    unfold path at sib
    rw [lpn, rpn, midn] at sib
    by_cases side : loc.val < mid.val
    · simp only [side, ↓reduceIte, List.append_assoc] at sib
      obtain ⟨x, hl, xe, xs, xc⟩ := ih lp half s loc e o _ halfv' (by omega) (by omega)
        (by omega) low (by omega) finish elems sib
      have after := drop_append sib
      rw [path_length, ← xc, ← xs] at after
      obtain ⟨room, value, -⟩ := drop_cons after
      obtain ⟨c, hc, cv⟩ := sibling_ok S x room
      refine ⟨{ x with cursor := c }, ?_, xe, xs, by simp [cv, xc]; omega⟩
      rw [traversal.reconstruct.eq_def]
      simp only [hstop, bind_ok]
      simp [c1, c2, c3, kids, hhalf, hmid, hl,
        outside S x rp half mid loc e (by omega) (Or.inr (by omega)), hc, collect_ok, node_ok,
        value]
    · simp only [side, ↓reduceIte] at sib
      obtain ⟨room, value, next⟩ := drop_cons sib
      obtain ⟨c, hc, cv⟩ := sibling_ok S o room
      obtain ⟨y, hr, ye, ys, yc⟩ := ih rp half mid loc e { o with cursor := c } rest halfv'
        (by omega) (by omega) (by omega) (by omega) (by omega) finish elems
        (by simpa [cv] using next)
      refine ⟨y, ?_, ye, ys, by simp [yc, cv]; omega⟩
      rw [traversal.reconstruct.eq_def]
      simp only [hstop, bind_ok]
      simp [c1, c2, c3, kids, hhalf, hmid, hr, hc, collect_ok, node_ok, value,
        outside S o lp half s loc e (by omega) (Or.inl (by omega))]

/-- The honest root of a snapshot of height `h` holding `items`. -/
def honestRoot (S : Scheme D M) (items : Std.U64 → Slice Std.U8) (h : Nat) : D :=
  S.hash (rootInput S domain (pos (2^h)) (tree S items h (2*(2^h-1)) 0))

/-- The honest siblings of `loc` in a snapshot of height `h`, as a slice. -/
def honestSiblings (S : Scheme D M) (items : Std.U64 → Slice Std.U8) (h : Nat) (loc : Std.U64)
    (bound : h ≤ 62) : Slice D :=
  Slice.from (path S items h (2*(2^h-1)) 0 loc.val) (by rw [path_length]; scalar_tac)

/-- On the honest siblings of an honest snapshot followed by `rest`, the production verifier
accepts exactly when `rest` is empty. -/
theorem honest_verify (S : Scheme D M) (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ 62)
    (loc : Std.U64) (inside : loc.val < 2^h.val) (ws : Slice D) (rest : List D)
    (siblings : ws.val = path S items h.val (2*(2^h.val-1)) 0 loc.val ++ rest) :
    client.verify S.terms () h loc (honestRoot S items h.val) (items loc) ws =
      RustM.ok (decide (rest = [])) := by
  have small : 2^h.val ≤ 2^62 := Nat.pow_le_pow_right (by decide) bound
  have one : 1 ≤ 2^h.val := Nat.one_le_two_pow
  obtain ⟨w, hw, wv⟩ := pow_ok h (by omega)
  have short : ¬ h > client.MAX_HEIGHT := by simp [client.MAX_HEIGHT]; scalar_tac
  have inside' : ¬ loc ≥ w := by scalar_tac
  obtain ⟨i, hi, iv⟩ := sub_ok w 1#u64 (by scalar_tac)
  obtain ⟨p, hp, pv⟩ := mul_ok 2#u64 i (by scalar_tac)
  obtain ⟨e, he, ev⟩ := add_ok loc 1#u64 (by scalar_tac)
  have pv' : p.val = 2*(2^h.val-1) := by simp at iv pv; omega
  obtain ⟨r, run, -, -, rc⟩ := honest_rec S items h.val p w 0#u64 loc e
    { nodes := (), elements := some (items loc), siblings := ws, cursor := 0#usize,
      collected := () } rest wv bound (by omega) (by simp; omega) (by simp) (by simp; omega)
    (by scalar_tac) rfl (by simp [siblings, pv'])
  have counted : r.cursor = Slice.len ws ↔ rest = [] := by
    have len : (Slice.len ws).val = h.val + rest.length := by simp [siblings, path_length]
    simp at rc
    constructor
    · intro same
      have := congrArg UScalar.val same
      rw [rc, len] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    · intro empty
      apply UScalar.eq_of_val_eq
      rw [rc, len, empty]
      rfl
  have rooted : S.hash (rootInput S domain w (tree S items h.val p.val 0)) =
      honestRoot S items h.val := by
    have : w = pos (2^h.val) := by rw [← wv, pos_val]
    simp [honestRoot, this, pv']
  unfold client.verify
  simp only [short, ↓reduceIte, hw, bind_ok, inside', hi, hp, he, traversal.Opening.new]
  rw [run]
  simp [traversal.Opening.impl.cursor, len_ok, root_eq, eq_ok]
  by_cases empty : rest = []
  · simp [counted.mpr empty, empty]
    exact rooted
  · simp [mt counted.mp empty, empty]

/-- The production verifier accepts every honest opening of an honest snapshot. -/
theorem honest_opening (S : Scheme D M) (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ 62)
    (loc : Std.U64) (inside : loc.val < 2^h.val) :
    client.verify S.terms () h loc (honestRoot S items h.val) (items loc)
      (honestSiblings S items h.val loc bound) = RustM.ok true := by
  simpa using honest_verify S items h bound loc inside _ [] (by simp [honestSiblings])

/-- The production verifier rejects an honest opening followed by an unused sibling. -/
theorem extra_sibling_rejected (S : Scheme D M) (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ 62) (loc : Std.U64) (inside : loc.val < 2^h.val) (ws : Slice D)
    (extra : D) (siblings : ws.val = path S items h.val (2*(2^h.val-1)) 0 loc.val ++ [extra]) :
    client.verify S.terms () h loc (honestRoot S items h.val) (items loc) ws = RustM.ok false := by
  simpa using honest_verify S items h bound loc inside ws [extra] siblings

/-! ## Totality -/

theorem sibling_total (S : Scheme D M) (o : Opening D) : ∃ res r,
    traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.sibling (mmr S) single element
      (noCollect D) o = RustM.ok (res, r) := by
  by_cases room : o.cursor.val < o.siblings.length
  · obtain ⟨c, hc, -⟩ := sibling_ok S o room
    exact ⟨_, _, hc⟩
  · exact ⟨_, _, sibling_end S o room⟩

theorem leaf_total (S : Scheme D M) (o : Opening D) (p : Std.U64) : ∃ res r,
    traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.leaf (mmr S) single element (noCollect D)
      o p = RustM.ok (res, r) := by
  cases h : o.elements with
  | some a => exact ⟨_, _, leaf_some S o a h p⟩
  | none =>
    refine ⟨.Err .MissingElements, { o with elements := none }, ?_⟩
    simp [traversal.Opening.Insts.Qmdb_dyleanTraversalBackend.leaf, h,
      client.Single.Insts.CoreIterTraitsIteratorIteratorElement.next]

/-- The production traversal returns, without panicking or diverging, on every subtree of an
MMR within the production size limit, whatever the siblings, elements and queried range. -/
theorem reconstruct_total (S : Scheme D M) (H : Nat) : ∀ (p w s loc e : Std.U64) (o : Opening D),
    w.val = 2^H → H ≤ 62 → 2*(w.val-1) ≤ p.val → s.val + w.val ≤ 2^62 →
    ∃ res r, traversal.reconstruct (backend S) o p w s loc e = RustM.ok (res, r) := by
  induction H with
  | zero =>
    intro p w s loc e o width _ _ bound
    simp at width
    by_cases off : s.val + w.val ≤ loc.val ∨ e.val ≤ s.val
    · rw [outside S o p w s loc e bound off]
      exact sibling_total S o
    rw [reconstruct_one S o p w s loc e width (by omega) (by omega) (by omega)]
    exact leaf_total S o p
  | succ n ih =>
    intro p w s loc e o width bound position start
    have one : 1 ≤ 2^n := Nat.one_le_two_pow
    have small : 2^n ≤ 2^61 := Nat.pow_le_pow_right (by decide) (by omega)
    have double : 2^(n+1) = 2*2^n := by rw [Nat.pow_succ]; omega
    by_cases off : s.val + w.val ≤ loc.val ∨ e.val ≤ s.val
    · rw [outside S o p w s loc e start off]
      exact sibling_total S o
    obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
    have c1 : ¬ stop.val ≤ loc.val := by omega
    have c2 : ¬ e.val ≤ s.val := by omega
    have c3 : ¬ w.val = 1 := by omega
    obtain ⟨lp, rp, kids, lpv, rpv⟩ := children_ok S p w (n+1) width bound (by omega) (by omega)
    obtain ⟨half, hhalf, halfv⟩ := UScalar.div_spec w (y := 2#u64) (by decide)
    have halfv' : half.val = 2^n := by simp at halfv; omega
    obtain ⟨mid, hmid, midv⟩ := add_ok s half (by scalar_tac)
    obtain ⟨res, x, hl⟩ := ih lp half s loc e o halfv' (by omega) (by omega) (by omega)
    rw [traversal.reconstruct.eq_def]
    simp only [hstop, bind_ok]
    cases res with
    | Err _ => simp [c1, c2, c3, kids, hhalf, hmid, hl]
    | Ok l =>
      obtain ⟨res', y, hr⟩ := ih rp half mid loc e x halfv' (by omega) (by omega) (by omega)
      cases res' with
      | Err _ => simp [c1, c2, c3, kids, hhalf, hmid, hl, hr]
      | Ok r => simp [c1, c2, c3, kids, hhalf, hmid, hl, hr, collect_ok, node_ok]

/-- The production verifier returns a verdict, without panicking or diverging, on every input. -/
theorem verify_total (S : Scheme D M) (h : Std.U32) (loc : Std.U64) (root : D) (item : Slice Std.U8)
    (ws : Slice D) : ∃ b, client.verify S.terms () h loc root item ws = RustM.ok b := by
  unfold client.verify
  by_cases tall : h.val > 62
  · have : h > client.MAX_HEIGHT := by simp [client.MAX_HEIGHT]; scalar_tac
    simp [this]
  · have short : ¬ h > client.MAX_HEIGHT := by simp [client.MAX_HEIGHT]; scalar_tac
    have small : 2^h.val ≤ 2^62 := Nat.pow_le_pow_right (by decide) (by omega)
    have one : 1 ≤ 2^h.val := Nat.one_le_two_pow
    obtain ⟨w, hw, wv⟩ := pow_ok h (by omega)
    by_cases out : loc.val ≥ 2^h.val
    · have : w.val ≤ loc.val := by omega
      simp [short, hw, this]
    · have inside : ¬ loc ≥ w := by scalar_tac
      obtain ⟨i, hi, iv⟩ := sub_ok w 1#u64 (by scalar_tac)
      obtain ⟨p, hp, pv⟩ := mul_ok 2#u64 i (by scalar_tac)
      obtain ⟨e, he, -⟩ := add_ok loc 1#u64 (by scalar_tac)
      obtain ⟨res, r, run⟩ := reconstruct_total S h.val p w 0#u64 loc e
        { nodes := (), elements := some item, siblings := ws, cursor := 0#usize, collected := () }
        wv (by omega) (by simp at iv pv; omega) (by simp; omega)
      simp only [short, ↓reduceIte, hw, bind_ok, inside, hi, hp, he, traversal.Opening.new, run]
      cases res with
      | Err _ => exact ⟨_, rfl⟩
      | Ok peak =>
        by_cases cur : r.cursor = Slice.len ws
        · exact ⟨decide (S.hash (rootInput S domain w peak) = root),
            by simp [traversal.Opening.impl.cursor, len_ok, root_eq, eq_ok, cur]⟩
        · exact ⟨false, by simp [traversal.Opening.impl.cursor, len_ok, root_eq, eq_ok, cur]⟩

/-! ## Production hashing over byte strings -/

omit [DecidableEq D] in
/-- Concatenated bytes keep hash inputs of one kind apart, because digests have one length. -/
theorem _root_.Qmdb.ByteHash.unambiguous (B : ByteHash D) : B.scheme.Unambiguous where
  leaf p a b same := by
    apply Slice.ext
    simpa [ByteHash.scheme] using same
  node p l r l' r' same := by
    have halves : B.bytes l ++ B.bytes r = B.bytes l' ++ B.bytes r' := by
      simpa [ByteHash.scheme] using same
    have split := List.append_inj halves (by rw [B.bytes_length, B.bytes_length])
    exact ⟨B.bytes_inj _ _ split.1, B.bytes_inj _ _ split.2⟩
  root d n x y same := by
    apply B.bytes_inj
    simpa [ByteHash.scheme] using same

/-- Position binding of the production verifier over byte strings: two openings that it accepts
at the same location under the same root carry the same item, or `finder` returns two different
byte strings with the same digest. -/
theorem byte_binding_or_collision (B : ByteHash D) (h : Std.U32) (loc : Std.U64) (root : D)
    (a b : Slice Std.U8) (wa wb : Slice D)
    (ha : client.verify B.scheme.terms () h loc root a wa = RustM.ok true)
    (hb : client.verify B.scheme.terms () h loc root b wb = RustM.ok true) :
    a = b ∨ ∃ x y : List Std.U8, finder B.scheme h loc a b wa wb = some (x, y) ∧ x ≠ y ∧
      B.hash x = B.hash y :=
  binding_or_collision B.scheme B.unambiguous h loc root a b wa wb ha hb

#print axioms binding_or_collision
#print axioms byte_binding_or_collision
#print axioms honest_opening
#print axioms extra_sibling_rejected
#print axioms verify_total

end
end Qmdb.Verifier
