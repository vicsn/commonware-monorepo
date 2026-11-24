module
public import Qmdb.Assumptions
public import Qmdb.MmrPeaks
public import Commonware.Symbolic.RustM

/-! The extracted verifier on DyLean terms. Uniqueness: two openings that it accepts at the same
location under the same root carry the same item and the same siblings. DyLean's hash and
concatenation are constructors, so a root term fixes every digest below it. Position binding is
the item half. The verifier also returns a verdict on every input and accepts every honest
opening. Checked by Lean; only the statements of `unique`, `verify_total`, `verify_bounds`,
`honest_opening` and `extra_sibling_rejected` matter for review. -/

namespace Qmdb.Verifier
open DY Aeneas Aeneas.Std Aeneas.Std.WP CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

/-! ## Digests as terms -/

/-- The big-endian bytes of a 64-bit integer. -/
def be (x : Std.U64) : Slice Std.U8 :=
  (Aeneas.Std.core.num.U64.to_be_bytes x).to_slice

/-- The digest of the leaf at position `p` holding `item`. -/
def leafTerm (p : Std.U64) (item : Slice Std.U8) : Bytes :=
  Hash.hash (chain [.Bytes (be p), .Bytes item])

/-- The digest of the node at position `p` with the given child digests. -/
def nodeTerm (p : Std.U64) (left right : Bytes) : Bytes :=
  Hash.hash (chain [.Bytes (be p), .Digest left, .Digest right])

/-- The root over one peak. -/
def rootTerm
    (domain : Aeneas.Std.Array Std.U8 2#usize) (leaves : Std.U64)
    (peak : Bytes) :
    Bytes :=
  Hash.hash (chain [.Bytes domain.to_slice, .Bytes (be leaves), .Digest peak])

theorem to_be_bytes_ok (x : Std.U64) :
    CoreModels.core.num.U64.to_be_bytes x = RustM.ok (Aeneas.Std.core.num.U64.to_be_bytes x) := by
  simp [CoreModels.core.num.U64.to_be_bytes, rust_primitives.arithmetic.to_be_bytes_u64]

theorem leaf_eq (u : Unit) (p : Std.U64) (item : Slice Std.U8) :
    terms.leaf_digest dyTerms u p item = RustM.ok (leafTerm p item) := by
  simp [terms.leaf_digest, to_be_bytes_ok, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, dyTerms, leafTerm, be]

theorem node_eq (u : Unit) (p : Std.U64) (left right : Bytes) :
    terms.node_digest dyTerms u p left right = RustM.ok (nodeTerm p left right) := by
  simp [terms.node_digest, to_be_bytes_ok, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, dyTerms, nodeTerm, be]

theorem root_eq (u : Unit) (domain : Aeneas.Std.Array Std.U8 2#usize) (leaves : Std.U64)
    (peak : Bytes) :
    terms.root dyTerms u domain leaves 0#u64 peak = RustM.ok (rootTerm domain leaves peak) := by
  simp [terms.root, to_be_bytes_ok, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, dyTerms, rootTerm, be]

/-- A leaf digest fixes its item: DyLean's hash and concatenation are constructors. -/
theorem leafTerm_inj {p : Std.U64} {a b : Slice Std.U8} (h : leafTerm p a = leafTerm p b) :
    a = b :=
  part_bytes_inj (concat_inj (Hash.hash_inj _ _ h)).2

/-- A node digest fixes both children. -/
theorem nodeTerm_inj {p : Std.U64} {l r l' r' : Bytes} (h : nodeTerm p l r = nodeTerm p l' r') :
    l = l' ∧ r = r' :=
  concat_inj (concat_inj (Hash.hash_inj _ _ h)).2

/-- A root fixes its peak. -/
theorem rootTerm_inj {domain : Aeneas.Std.Array Std.U8 2#usize} {n : Std.U64} {x y : Bytes}
    (h : rootTerm domain n x = rootTerm domain n y) : x = y :=
  (concat_inj (concat_inj (Hash.hash_inj _ _ h)).2).2

/-! ## The size bound -/

/-- The largest height that the client accepts: the extracted `MAX_HEIGHT`. -/
def maxHeight : Nat := qmdb.MAX_HEIGHT.val

/-- The most leaves of a tree that the client accepts, which is production's limit on an MMR. -/
def maxLeaves : Nat := 2 ^ maxHeight

/-- The value of the bound. Every other statement and proof names it. -/
theorem maxHeight_eq : maxHeight = 62 := by
  simp [maxHeight, qmdb.MAX_HEIGHT]

/-- The client accepts trees of two leaves, which the sanity checks use. -/
theorem one_le_maxHeight : 1 ≤ maxHeight := by
  rw [maxHeight_eq]
  decide

/-- The client's height check, read on natural numbers. -/
theorem above_maxHeight (h : Std.U32) : h > qmdb.MAX_HEIGHT ↔ h.val > maxHeight :=
  Iff.rfl

/-- A tree within the height bound is within the leaf bound. -/
theorem leaves_le_maxLeaves {h : Nat} (bound : h ≤ maxHeight) : 2 ^ h ≤ maxLeaves :=
  Nat.pow_le_pow_right (by decide) bound

/-- Twice the leaves of the largest tree fit 64 bits, so every position and range end does. -/
theorem maxLeaves_fits : 2 * maxLeaves ≤ 2 ^ 64 := by
  rw [maxLeaves, maxHeight_eq]
  decide

/-! ## The production backend -/

/-- The production MMR geometry. -/
abbrev mmrGeometry := geometry.Mmr.Insts.Commonware_symbolicReconstructGeometryPeaks
/-- The nodes of the production MMR geometry, with the production encodings. -/
abbrev Nodes := reconstruct.StandardNodes geometry.Mmr Unit
/-- The client's opening: MMR nodes, one claimed item, siblings as terms and no collector. -/
abbrev Opening := traversal.Opening Nodes reconstruct.Single Unit Bytes
/-- The production MMR geometry and encodings, hashing with `dyTerms`. -/
abbrev mmr := reconstruct.StandardNodes.Insts.Commonware_symbolicTraversalNodes mmrGeometry dyTerms
/-- The production element source that yields the one claimed item. -/
abbrev single := reconstruct.Single.Insts.CoreIterTraitsIteratorIteratorElement
/-- The production reading of that element as bytes. -/
abbrev element := reconstruct.Element.Insts.CoreConvertAsRefSliceU8
/-- The extracted collector that records nothing. -/
abbrev noCollect := Tuple.Insts.Commonware_symbolicTraversalCollect Bytes
/-- The extracted production backend of the traversal, over those four. -/
abbrev backend :=
  traversal.Opening.Insts.Commonware_symbolicTraversalBackend mmr single element noCollect

theorem index_ok {α} (s : Slice α) (i : Std.Usize) (bound : i.val < s.length) :
    Slice.index_usize s i = RustM.ok s.val[i.val] := by
  obtain ⟨x, hx, _, rfl⟩ := ok_of_partialSpec (Slice.index_usize_spec s i)
    (by intro e; cases e <;> simp; omega) (by simp)
  exact hx

theorem sibling_ok (o : Opening) (room : o.cursor.val < o.siblings.length) :
    ∃ c : Std.Usize, traversal.Opening.Insts.Commonware_symbolicTraversalBackend.sibling mmr single
      element noCollect o =
        RustM.ok (.Ok o.siblings.val[o.cursor.val], { o with cursor := c }) ∧
      c.val = o.cursor.val + 1 := by
  obtain ⟨c, hc, cv⟩ := succ_ok o.cursor o.siblings room
  refine ⟨c, ?_, cv⟩
  have roomv : o.cursor.val < o.siblings.val.length := room
  simp [traversal.Opening.Insts.Commonware_symbolicTraversalBackend.sibling,
    CoreModels.core.slice.Slice.get, roomv,
    CoreModels.core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    rust_primitives.slice.slice_length,
    rust_primitives.slice.slice_index, index_ok o.siblings o.cursor room, hc]

theorem sibling_end (o : Opening)
    (none_left : ¬ o.cursor.val < o.siblings.length) :
    traversal.Opening.Insts.Commonware_symbolicTraversalBackend.sibling mmr single element
      noCollect o = RustM.ok (.Err .MissingDigests, o) := by
  have endv : ¬ o.cursor.val < o.siblings.val.length := none_left
  simp [traversal.Opening.Insts.Commonware_symbolicTraversalBackend.sibling,
    CoreModels.core.slice.Slice.get, endv,
    CoreModels.core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    rust_primitives.slice.slice_length]

/-- A sibling read that succeeds returns the next unread sibling and keeps the element source. -/
theorem sibling_read (o x : Opening) (d : Bytes)
    (h : traversal.Opening.Insts.Commonware_symbolicTraversalBackend.sibling mmr single element
      noCollect o = RustM.ok (.Ok d, x)) :
    o.siblings.val.drop o.cursor.val = d :: x.siblings.val.drop x.cursor.val ∧
      x.siblings = o.siblings ∧ x.elements = o.elements := by
  by_cases room : o.cursor.val < o.siblings.length
  · obtain ⟨c, hc, cv⟩ := sibling_ok o room
    rw [hc] at h
    have same := ok_inj h
    simp only [Prod.mk.injEq, CoreModels.core.result.Result.Ok.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    refine ⟨?_, rfl, rfl⟩
    have roomv : o.cursor.val < o.siblings.val.length := room
    simp only [cv]
    exact List.drop_eq_getElem_cons roomv
  · rw [sibling_end o room] at h
    have same := ok_inj h
    simp at same

theorem leaf_some (o : Opening) (a : Slice Std.U8) (h : o.elements = some a)
    (p : Std.U64) :
    traversal.Opening.Insts.Commonware_symbolicTraversalBackend.leaf mmr single element noCollect
      o p = RustM.ok (.Ok (leafTerm p a), { o with elements := none }) := by
  simp [traversal.Opening.Insts.Commonware_symbolicTraversalBackend.leaf, h,
    reconstruct.Single.Insts.CoreIterTraitsIteratorIteratorElement.next,
    reconstruct.Element.Insts.CoreConvertAsRefSliceU8.as_ref,
    reconstruct.StandardNodes.Insts.Commonware_symbolicTraversalNodes.leaf_digest, leaf_eq]

theorem ilog2_ok (w : Std.U64) (n : Nat) (hw : w.val = 2 ^ n) :
    CoreModels.core.num.U64.ilog2 w = RustM.ok (⟨BitVec.ofNat 32 n⟩ : Std.U32) := by
  simp [CoreModels.core.num.U64.ilog2, rust_primitives.arithmetic.ilog2_u64, uilog2, hw,
    Nat.log2_two_pow]

theorem children_ok (p w : Std.U64) (n : Nat) (hw : w.val = 2 ^ n) (hn : n ≤ maxHeight)
    (hp : w.val ≤ p.val) (one : 1 ≤ p.val) :
    ∃ lp rp : Std.U64, (∀ o : Opening,
      traversal.Opening.Insts.Commonware_symbolicTraversalBackend.children mmr single element
        noCollect o p w = RustM.ok (lp, rp)) ∧ lp.val = p.val - w.val ∧
      rp.val = p.val - 1 := by
  have top := maxHeight_eq
  have height : (⟨BitVec.ofNat 32 n⟩ : Std.U32).val = n := by
    change (BitVec.ofNat 32 n).toNat = n
    simp
    omega
  obtain ⟨z, hz, zv⟩ := pow_ok ⟨BitVec.ofNat 32 n⟩ (by omega)
  rw [height] at zv
  obtain ⟨lp, hlp, lpv⟩ := sub_ok p z (by omega)
  obtain ⟨rp, hrp, rpv⟩ := sub_ok p 1#u64 (by scalar_tac)
  refine ⟨lp, rp, fun o => ?_, by omega, by simpa using rpv⟩
  simp [traversal.Opening.Insts.Commonware_symbolicTraversalBackend.children, ilog2_ok w n hw,
    reconstruct.StandardNodes.Insts.Commonware_symbolicTraversalNodes.children,
    geometry.Mmr.Insts.Commonware_symbolicReconstructGeometryPeaks.children,
    mmr_geometry.children, hz, hlp, hrp]

theorem collect_ok (o : Opening) (lp : Std.U64) (l : Bytes) (rp : Std.U64)
    (r : Bytes) :
    traversal.Opening.Insts.Commonware_symbolicTraversalBackend.collect mmr single element
      noCollect o lp l rp r = RustM.ok o := by
  simp [traversal.Opening.Insts.Commonware_symbolicTraversalBackend.collect,
    Tuple.Insts.Commonware_symbolicTraversalCollect.collect]

theorem node_ok (o : Opening) (p w s : Std.U64) {n : Nat} (hw : w.val = 2 ^ n) (l r : Bytes) :
    traversal.Opening.Insts.Commonware_symbolicTraversalBackend.node mmr single element noCollect
      o p w s l r = RustM.ok (nodeTerm p l r) := by
  simp [traversal.Opening.Insts.Commonware_symbolicTraversalBackend.node, ilog2_ok w n hw,
    reconstruct.StandardNodes.Insts.Commonware_symbolicTraversalNodes.node_digest, node_eq]

/-- A subtree outside the queried range is read as one sibling. -/
theorem outside (o : Opening) (p w s loc e : Std.U64)
    (bound : s.val + w.val ≤ maxLeaves) (off : s.val + w.val ≤ loc.val ∨ e.val ≤ s.val) :
    traversal.reconstruct backend o p w s loc e =
      traversal.Opening.Insts.Commonware_symbolicTraversalBackend.sibling mmr single element
        noCollect o := by
  have fits := maxLeaves_fits
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
theorem reconstruct_one (o : Opening) (p w s loc e : Std.U64)
    (hw : w.val = 1) (c1 : ¬ s.val + 1 ≤ loc.val) (c2 : ¬ e.val ≤ s.val) :
    traversal.reconstruct backend o p w s loc e =
      traversal.Opening.Insts.Commonware_symbolicTraversalBackend.leaf mmr single element
        noCollect o p := by
  obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
  have c1' : ¬ stop.val ≤ loc.val := by omega
  have c3 : w = 1#u64 := by scalar_tac
  rw [traversal.reconstruct.eq_def]
  simp only [hstop, bind_ok]
  simp [c1', c2, c3]

theorem reconstruct_leaf (o : Opening) (a : Slice Std.U8)
    (h : o.elements = some a) (p w s loc e : Std.U64) (hw : w.val = 1)
    (inside : s.val ≤ loc.val ∧ loc.val < s.val + 1) (finish : e.val = loc.val + 1) :
    traversal.reconstruct backend o p w s loc e =
      RustM.ok (.Ok (leafTerm p a), { o with elements := none }) := by
  rw [reconstruct_one o p w s loc e hw (by omega) (by omega), leaf_some o a h p]

/-! ## The digest of an opening -/

/-- The 64-bit integer with value `x`, for `x < 2 ^ 64`. -/
def pos (x : Nat) : Std.U64 := ⟨BitVec.ofNat 64 x⟩

theorem pos_val (x : Std.U64) : pos x.val = x := by
  apply UScalar.eq_of_val_eq
  change (BitVec.ofNat 64 x.val).toNat = x.val
  have : x.val < 2 ^ 64 := by scalar_tac
  simp

/-- The digest that an opening rebuilds for the height-`n` subtree at position `p` with first leaf
`s`, for `item` at leaf `loc` and the siblings `ws`, and the siblings that it leaves unread. -/
def rebuild (item : Slice Std.U8) (loc : Nat) :
    Nat → Nat → Nat → List Bytes → Option (Bytes × List Bytes)
  | 0, p, _, ws => some (leafTerm (pos p) item, ws)
  | n + 1, p, s, ws =>
    if loc < s + 2 ^ n then
      match rebuild item loc n (p - 2 ^ (n + 1)) s ws with
      | some (left, right :: rest) => some (nodeTerm (pos p) left right, rest)
      | _ => none
    else
      match ws with
      | left :: ws =>
        match rebuild item loc n (p - 1) (s + 2 ^ n) ws with
        | some (right, rest) => some (nodeTerm (pos p) left right, rest)
        | none => none
      | [] => none

theorem rebuild_left {item : Slice Std.U8} {loc n p s : Nat} {ws rest : List Bytes} {d : Bytes}
    (side : loc < s + 2 ^ n) (h : rebuild item loc (n + 1) p s ws = some (d, rest)) :
    ∃ left right, rebuild item loc n (p - 2 ^ (n + 1)) s ws = some (left, right :: rest) ∧
      d = nodeTerm (pos p) left right := by
  rw [rebuild.eq_def] at h
  simp only [side, ↓reduceIte] at h
  cases below : rebuild item loc n (p - 2 ^ (n + 1)) s ws with
  | none => simp [below] at h
  | some found =>
    obtain ⟨left, unread⟩ := found
    cases unread with
    | nil => simp [below] at h
    | cons right rest' =>
      simp only [below, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨left, right, rfl, rfl⟩

theorem rebuild_right {item : Slice Std.U8} {loc n p s : Nat} {ws rest : List Bytes} {d : Bytes}
    (side : ¬ loc < s + 2 ^ n) (h : rebuild item loc (n + 1) p s ws = some (d, rest)) :
    ∃ left ws' right, ws = left :: ws' ∧
      rebuild item loc n (p - 1) (s + 2 ^ n) ws' = some (right, rest) ∧
      d = nodeTerm (pos p) left right := by
  rw [rebuild.eq_def] at h
  simp only [side, ↓reduceIte] at h
  cases ws with
  | nil => simp at h
  | cons left ws' =>
    cases below : rebuild item loc n (p - 1) (s + 2 ^ n) ws' with
    | none => simp [below] at h
    | some found =>
      obtain ⟨right, unread⟩ := found
      simp only [below, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨left, ws', right, rfl, below, rfl⟩

/-- A successful run of the production traversal over a subtree that holds the queried location
returns the digest of `rebuild` and leaves the siblings that `rebuild` leaves unread. -/
theorem reconstruct_rebuild (H : Nat) : ∀ (p w s loc e : Std.U64)
    (o r : Opening) (item : Slice Std.U8) (d : Bytes), w.val = 2 ^ H → H ≤ maxHeight →
    2 * (w.val - 1) ≤ p.val → s.val + w.val ≤ maxLeaves → s.val ≤ loc.val →
    loc.val < s.val + w.val → e.val = loc.val + 1 → o.elements = some item →
    traversal.reconstruct backend o p w s loc e = RustM.ok (.Ok d, r) →
    rebuild item loc.val H p.val s.val (o.siblings.val.drop o.cursor.val) =
      some (d, r.siblings.val.drop r.cursor.val) ∧ r.siblings = o.siblings := by
  induction H with
  | zero =>
    intro p w s loc e o r item d width _ _ bound low high finish elems run
    simp at width
    rw [reconstruct_leaf o item elems p w s loc e width ⟨low, by omega⟩ finish]
      at run
    have same := ok_inj run
    simp only [Prod.mk.injEq, CoreModels.core.result.Result.Ok.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨by simp [rebuild, pos_val], rfl⟩
  | succ n ih =>
    intro p w s loc e o r item d width bound position start low high finish elems run
    have one : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have fits := maxLeaves_fits
    have double : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
    have c1 : ¬ stop.val ≤ loc.val := by omega
    have c2 : ¬ e.val ≤ s.val := by omega
    have c3 : ¬ w.val = 1 := by omega
    obtain ⟨lp, rp, kids, lpv, rpv⟩ := children_ok p w (n + 1) width bound (by omega) (by omega)
    obtain ⟨half, hhalf, halfv⟩ := UScalar.div_spec w (y := 2#u64) (by decide)
    have halfv' : half.val = 2 ^ n := by simp at halfv; omega
    obtain ⟨mid, hmid, midv⟩ := add_ok s half (by scalar_tac)
    have lpn : p.val - 2 ^ (n + 1) = lp.val := by omega
    have rpn : p.val - 1 = rp.val := by omega
    have midn : s.val + 2 ^ n = mid.val := by omega
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
        simp [collect_ok, node_ok _ _ _ _ width] at k'
        obtain ⟨rfl, rfl⟩ := k'
        by_cases side : loc.val < mid.val
        · obtain ⟨below, xs⟩ := ih lp half s loc e o x item l halfv' (by omega)
            (by omega) (by omega) low (by omega) finish elems hl
          rw [outside x rp half mid loc e (by omega) (Or.inr (by omega))] at hr
          obtain ⟨unread, ys, -⟩ := sibling_read x y rr hr
          rw [unread] at below
          refine ⟨?_, ys.trans xs⟩
          rw [rebuild.eq_def]
          simp only [midn, side, ↓reduceIte, lpn, below, pos_val]
        · rw [outside o lp half s loc e (by omega) (Or.inl (by omega))] at hl
          obtain ⟨unread, xs, xe⟩ := sibling_read o x l hl
          obtain ⟨below, ys⟩ := ih rp half mid loc e x y item rr halfv' (by omega)
            (by omega) (by omega) (by omega) (by omega) finish (xe.trans elems) hr
          refine ⟨?_, ys.trans xs⟩
          rw [rebuild.eq_def]
          simp only [midn, side, ↓reduceIte, unread, rpn, below, pos_val]

/-- Two openings that rebuild the same digest for a subtree carry the same item and have read the
same siblings: the digest is a term, and it fixes the terms below it. -/
theorem rebuild_inj (a b : Slice Std.U8) (loc : Nat) (n : Nat) : ∀ (p s : Nat)
    (wa wb : List Bytes) (d : Bytes) (ra rb : List Bytes),
    rebuild a loc n p s wa = some (d, ra) → rebuild b loc n p s wb = some (d, rb) →
    a = b ∧ ∃ read, wa = read ++ ra ∧ wb = read ++ rb := by
  induction n with
  | zero =>
    intro p s wa wb d ra rb h₁ h₂
    simp only [rebuild, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨same, rfl⟩ := h₂
    exact ⟨(leafTerm_inj same).symm, [], rfl, rfl⟩
  | succ n ih =>
    intro p s wa wb d ra rb h₁ h₂
    by_cases side : loc < s + 2 ^ n
    · obtain ⟨l₁, x₁, below₁, rfl⟩ := rebuild_left side h₁
      obtain ⟨l₂, x₂, below₂, same⟩ := rebuild_left side h₂
      obtain ⟨child, sibling⟩ := nodeTerm_inj same
      rw [← child, ← sibling] at below₂
      obtain ⟨eq, read, ha, hb⟩ := ih _ _ _ _ _ _ _ below₁ below₂
      exact ⟨eq, read ++ [x₁], by simp [ha], by simp [hb]⟩
    · obtain ⟨l₁, wa', r₁, rfl, below₁, rfl⟩ := rebuild_right side h₁
      obtain ⟨l₂, wb', r₂, rfl, below₂, same⟩ := rebuild_right side h₂
      obtain ⟨sibling, child⟩ := nodeTerm_inj same
      rw [← child] at below₂
      obtain ⟨eq, read, ha, hb⟩ := ih _ _ _ _ _ _ _ below₁ below₂
      exact ⟨eq, l₁ :: read, by simp [ha], by simp [hb, sibling]⟩

/-! ## The verifier -/

/-- The two domain bytes of the client's root, read from the extraction. -/
abbrev domain : Aeneas.Std.Array Std.U8 2#usize :=
  Array.make 2#usize [mmr_geometry.DOMAIN, qmdb.BACKWARD_FOLD]

theorem eq_ok (a b : Bytes) :
    dyTerms.corecmpPartialEqInst.eq a b = RustM.ok (decide (a = b)) :=
  rfl

/-- The opening the client's traversal starts from. -/
abbrev start (item : Slice Std.U8) (ws : Slice Bytes) : Opening :=
  { nodes := ⟨(), ()⟩, elements := .Some item, siblings := ws, cursor := 0#usize,
    collected := () }

/-- The client's verdict once the traversal of its one peak has returned `r` and left `o`. -/
def verdict (w : Std.U64) (root : Bytes) (ws : Slice Bytes)
    (r : CoreModels.core.result.Result Bytes traversal.Error) (o : Opening) : Bool :=
  match r with
  | .Ok peak => decide (o.elements = .None ∧ o.cursor.val = ws.val.length ∧
      rootTerm domain w peak = root)
  | .Err _ => false

/-- Inside the bound on the height and the tree, the client runs the production traversal of its
one peak from the first sibling, provided it was given exactly `h` siblings. -/
theorem verify_eq (h : Std.U32) (bound : h.val ≤ maxHeight) (loc : Std.U64) (root : Bytes)
    (item : Slice Std.U8) (ws : Slice Bytes) (inside : loc.val < 2 ^ h.val) :
    ∃ (w p e : Std.U64), w.val = 2 ^ h.val ∧ p.val = 2 * (2 ^ h.val - 1) ∧
      e.val = loc.val + 1 ∧
      qmdb.verify dyTerms () h loc root item ws =
        if ws.val.length = h.val then (do
          let (r, o) ← traversal.reconstruct backend (start item ws) p w 0#u64 loc e
          RustM.ok (verdict w root ws r o))
        else RustM.ok false := by
  have top := maxHeight_eq
  have short : ¬ h > qmdb.MAX_HEIGHT := mt (above_maxHeight h).mp (by omega)
  obtain ⟨leaves, hl, lv⟩ := Reconstruct.width_ok h (by omega)
  obtain ⟨st, p, hh, hpeaks, pv, hhv, yields⟩ := MmrPeaks.single_peak h.val (by omega) leaves lv
  have same : hh = h := UScalar.eq_of_val_eq hhv
  subst same
  have pow : 2 ^ hh.val ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨w, ls, e, first, wv, lsv, ev, firstv, run⟩ := Reconstruct.reconstruct_single
    mmrGeometry mmr () ⟨(), ()⟩ domain true leaves 0#usize ws loc item [] [] p hh st
    mmr_geometry.MAX_LEAVES
    (by simp [geometry.Mmr.Insts.Commonware_symbolicReconstructGeometryPeaks.max_leaves])
    (by simp [mmr_geometry.MAX_LEAVES]; omega) (by simp [mmr_geometry.MAX_LEAVES])
    (by simp [geometry.Mmr.Insts.Commonware_symbolicReconstructGeometryPeaks.peaks, hpeaks])
    yields (by simp [Reconstruct.Low]; omega) (by simp [Reconstruct.span, lv])
    (by simp [Reconstruct.span]; omega) (by simp) (by simp)
  have first0 : first = 0#usize := UScalar.eq_of_val_eq (by
    rw [firstv]
    simp [Reconstruct.siblingsStartOf, Reconstruct.afterStartOf, Reconstruct.foldOf,
      Reconstruct.individualOf])
  have ls0 : ls = 0#u64 := UScalar.eq_of_val_eq (by rw [lsv]; simp [Reconstruct.span])
  subst first0 ls0
  refine ⟨w, p, e, wv, by omega, ev, ?_⟩
  unfold qmdb.verify
  simp only [short, ↓reduceIte, hl, bind_ok, reconstruct.StandardNodes.new,
    reconstruct.Single.new]
  have wl : w = leaves := UScalar.eq_of_val_eq (by omega)
  subst wl
  have zero : (0#usize).val = 0 := rfl
  simp only [zero, Nat.zero_add] at run ⊢
  rw [run]
  by_cases len : ws.val.length = hh.val
  · simp only [len, Nat.lt_irrefl, ↓reduceIte]
    generalize traversal.reconstruct _ _ p w 0#u64 loc e = T
    simp
    have bag (peak : Bytes) : Reconstruct.bagRoot domain true w (UScalar.cast .U64 0#usize)
        (Reconstruct.toFoldOf true 0 0)
        (Reconstruct.listed ws.val (Reconstruct.afterStartOf true 0 0)
          (Reconstruct.siblingsStartOf true 0 0 0) peak) = some (rootTerm domain w peak) := by
      simp [Reconstruct.bagRoot, Reconstruct.toFoldOf, Reconstruct.foldOf, Reconstruct.listed,
        Reconstruct.afterStartOf, Reconstruct.siblingsStartOf, Reconstruct.individualOf,
        Reconstruct.bagWith, Reconstruct.rootTerm, rootTerm, Reconstruct.be, be]
    congr 1
    funext x
    obtain ⟨r, o⟩ := x
    cases r with
    | Err err => cases err <;> simp [Reconstruct.outcome, verdict]
    | Ok peak =>
      cases helem : o.elements <;> simp [Reconstruct.outcome, verdict, helem, bag, eq_ok]
      by_cases cur : o.cursor.val = ws.val.length <;> simp [cur]
  · rcases Nat.lt_or_gt_of_ne len with lt | gt
    · simp [lt, len]
    · have c1 : ¬ ws.val.length < hh.val := by omega
      simp [c1, gt, len]

/-- Outside the tree the client rejects. -/
theorem verify_outside (h : Std.U32) (bound : h.val ≤ maxHeight) (loc : Std.U64) (root : Bytes)
    (item : Slice Std.U8) (ws : Slice Bytes) (out : 2 ^ h.val ≤ loc.val) :
    qmdb.verify dyTerms () h loc root item ws = RustM.ok false := by
  have top := maxHeight_eq
  have short : ¬ h > qmdb.MAX_HEIGHT := mt (above_maxHeight h).mp (by omega)
  obtain ⟨leaves, hl, lv⟩ := Reconstruct.width_ok h (by omega)
  have pow : 2 ^ h.val ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨err, run⟩ := Reconstruct.reconstruct_outside mmrGeometry mmr () ⟨(), ()⟩ domain true
    leaves 0#usize ws loc item mmr_geometry.MAX_LEAVES
    (by simp [geometry.Mmr.Insts.Commonware_symbolicReconstructGeometryPeaks.max_leaves])
    (by omega)
  unfold qmdb.verify
  simp only [short, ↓reduceIte, hl, bind_ok, reconstruct.StandardNodes.new,
    reconstruct.Single.new]
  rw [run]
  simp

/-- What an accepting `verify` has checked. -/
theorem verify_true {h : Std.U32} {loc : Std.U64} {root : Bytes}
    {item : Slice Std.U8} {ws : Slice Bytes}
    (acc : qmdb.verify dyTerms () h loc root item ws = RustM.ok true) :
    h.val ≤ maxHeight ∧ loc.val < 2 ^ h.val ∧ ∃ (w p e : Std.U64) (peak : Bytes) (r : Opening),
      w.val = 2 ^ h.val ∧ p.val = 2 * (2 ^ h.val - 1) ∧ e.val = loc.val + 1 ∧
      traversal.reconstruct backend (start item ws) p w 0#u64 loc e = RustM.ok (.Ok peak, r) ∧
      rootTerm domain w peak = root ∧ r.cursor.val = ws.val.length := by
  have top := maxHeight_eq
  by_cases tall : h.val > maxHeight
  · have : h > qmdb.MAX_HEIGHT := (above_maxHeight h).mpr tall
    unfold qmdb.verify at acc
    simp [this] at acc
  by_cases out : 2 ^ h.val ≤ loc.val
  · rw [verify_outside h (by omega) loc root item ws out] at acc
    simp at acc
  obtain ⟨w, p, e, wv, pv, ev, run⟩ := verify_eq h (by omega) loc root item ws (by omega)
  rw [run] at acc
  split at acc
  · obtain ⟨⟨res, r⟩, hrun, k⟩ := bind_eq_ok acc
    cases res with
    | Err _ => simp [verdict] at k
    | Ok peak =>
      simp [verdict] at k
      exact ⟨by omega, by omega, w, p, e, peak, r, wv, pv, ev, hrun, k.2.2, k.2.1⟩
  · simp at acc

/-- The extracted verifier accepts only heights up to the bound and locations
inside the tree. -/
theorem verify_bounds
    {h : Std.U32} {loc : Std.U64} {root : Bytes}
    {item : Slice Std.U8} {ws : Slice Bytes}
    (acc : qmdb.verify dyTerms () h loc root item ws = RustM.ok true) :
    h.val ≤ maxHeight ∧
    loc.val < 2 ^ h.val :=
  let ⟨height, inside, _⟩ := verify_true acc
  ⟨height, inside⟩

/-- An accepting `verify` has rebuilt a peak from all of its siblings, and the root over that peak
is `root`. -/
theorem verify_rebuild {h : Std.U32} {loc : Std.U64} {root : Bytes} {item : Slice Std.U8}
    {ws : Slice Bytes} (acc : qmdb.verify dyTerms () h loc root item ws = RustM.ok true) :
    ∃ peak, rebuild item loc.val h.val (2 * (2 ^ h.val - 1)) 0 ws.val = some (peak, []) ∧
      rootTerm domain (pos (2 ^ h.val)) peak = root := by
  obtain ⟨hh, hl, w, p, e, peak, r, wv, pv, ev, run, rooted, used⟩ := verify_true acc
  have small : 2 ^ h.val ≤ maxLeaves := leaves_le_maxLeaves hh
  obtain ⟨path, kept⟩ := reconstruct_rebuild h.val p w 0#u64 loc e _ r item peak wv hh
    (by omega) (by simp; omega) (by simp) (by simp; omega) ev rfl run
  have width : w = pos (2 ^ h.val) := by rw [← wv, pos_val]
  have none_left : r.siblings.val.drop r.cursor.val = [] := by
    simp only [kept, used, List.drop_length]
  refine ⟨peak, ?_, width ▸ rooted⟩
  simpa [pv, none_left] using path

/-- Uniqueness of accepted openings: two openings that the extracted verifier
accepts at the same location under the same root carry the same item and the
same siblings. Position binding is the item half. -/
theorem unique
    (h : Std.U32) (loc : Std.U64) (root : Bytes)
    (a b : Slice Std.U8) (wa wb : Slice Bytes)
    (ha : qmdb.verify dyTerms () h loc root a wa = RustM.ok true)
    (hb : qmdb.verify dyTerms () h loc root b wb = RustM.ok true) :
    a = b ∧
    wa = wb := by
  obtain ⟨peak₁, path₁, root₁⟩ := verify_rebuild ha
  obtain ⟨peak₂, path₂, root₂⟩ := verify_rebuild hb
  obtain rfl := rootTerm_inj (root₁.trans root₂.symm)
  obtain ⟨same, read, ra, rb⟩ := rebuild_inj a b loc.val h.val _ _ _ _ _ _ _ path₁ path₂
  exact ⟨same, Slice.ext _ _ (by simpa using ra.trans rb.symm)⟩

/-! ## Honest openings -/

/-- The honest digest of the height-`n` subtree at position `p` whose first leaf
is `s`. -/
def tree (items : Std.U64 → Slice Std.U8) : Nat → Nat → Nat → Bytes
  | 0, p, s => leafTerm (pos p) (items (pos s))
  | n + 1, p, s =>
    nodeTerm (pos p)
      (tree items n (p - 2 ^ (n + 1)) s)
      (tree items n (p - 1) (s + 2 ^ n))

/-- The honest siblings of leaf `loc` in that subtree, in the order the
traversal reads them. -/
def path (items : Std.U64 → Slice Std.U8) : Nat → Nat → Nat → Nat → List Bytes
  | 0, _, _, _ => []
  | n + 1, p, s, loc =>
    if loc < s + 2 ^ n then
      path items n (p - 2 ^ (n + 1)) s loc ++ [tree items n (p - 1) (s + 2 ^ n)]
    else
      tree items n (p - 2 ^ (n + 1)) s :: path items n (p - 1) (s + 2 ^ n) loc

theorem path_length (items : Std.U64 → Slice Std.U8) (n : Nat) :
    ∀ p s loc, (path items n p s loc).length = n := by
  induction n with
  | zero => intros; rfl
  | succ n ih => intro p s loc; unfold path; split <;> simp [ih]

theorem drop_cons {α} {l : List α} {c : Nat} {x : α} {t : List α} (h : l.drop c = x :: t) :
    ∃ hc : c < l.length, l[c] = x ∧ l.drop (c + 1) = t := by
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
theorem honest_rec (items : Std.U64 → Slice Std.U8) (H : Nat) :
    ∀ (p w s loc e : Std.U64) (o : Opening) (rest : List Bytes), w.val = 2 ^ H → H ≤ maxHeight →
    2 * (w.val - 1) ≤ p.val → s.val + w.val ≤ maxLeaves → s.val ≤ loc.val →
    loc.val < s.val + w.val → e.val = loc.val + 1 → o.elements = some (items loc) →
    o.siblings.val.drop o.cursor.val = path items H p.val s.val loc.val ++ rest →
    ∃ r : Opening, traversal.reconstruct backend o p w s loc e =
      RustM.ok (.Ok (tree items H p.val s.val), r) ∧ r.elements = none ∧
      r.siblings = o.siblings ∧ r.cursor.val = o.cursor.val + H := by
  induction H with
  | zero =>
    intro p w s loc e o rest width _ _ bound low high finish elems _
    simp at width
    have at_loc : s = loc := UScalar.eq_of_val_eq (by omega)
    subst at_loc
    refine ⟨{ o with elements := none }, ?_, rfl, rfl, rfl⟩
    rw [reconstruct_leaf o (items s) elems p w s s e width ⟨low, by omega⟩ finish]
    simp [tree, pos_val]
  | succ n ih =>
    intro p w s loc e o rest width bound position start low high finish elems sib
    have one : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have fits := maxLeaves_fits
    have double : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
    have c1 : ¬ stop.val ≤ loc.val := by omega
    have c2 : ¬ e.val ≤ s.val := by omega
    have c3 : ¬ w.val = 1 := by omega
    obtain ⟨lp, rp, kids, lpv, rpv⟩ := children_ok p w (n + 1) width bound (by omega) (by omega)
    obtain ⟨half, hhalf, halfv⟩ := UScalar.div_spec w (y := 2#u64) (by decide)
    have halfv' : half.val = 2 ^ n := by simp at halfv; omega
    obtain ⟨mid, hmid, midv⟩ := add_ok s half (by scalar_tac)
    have lpn : p.val - 2 ^ (n + 1) = lp.val := by omega
    have rpn : p.val - 1 = rp.val := by omega
    have midn : s.val + 2 ^ n = mid.val := by omega
    have whole : tree items (n + 1) p.val s.val =
        nodeTerm p (tree items n lp.val s.val) (tree items n rp.val mid.val) := by
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
      obtain ⟨c, hc, cv⟩ := sibling_ok x room
      refine ⟨{ x with cursor := c }, ?_, xe, xs, by simp [cv, xc]; omega⟩
      rw [traversal.reconstruct.eq_def]
      simp only [hstop, bind_ok]
      simp [c1, c2, c3, kids, hhalf, hmid, hl,
        outside x rp half mid loc e (by omega) (Or.inr (by omega)), hc, collect_ok,
        node_ok _ _ _ _ width, value]
    · simp only [side, ↓reduceIte] at sib
      obtain ⟨room, value, next⟩ := drop_cons sib
      obtain ⟨c, hc, cv⟩ := sibling_ok o room
      obtain ⟨y, hr, ye, ys, yc⟩ := ih rp half mid loc e { o with cursor := c } rest halfv'
        (by omega) (by omega) (by omega) (by omega) (by omega) finish elems
        (by simpa [cv] using next)
      refine ⟨y, ?_, ye, ys, by simp [yc, cv]; omega⟩
      rw [traversal.reconstruct.eq_def]
      simp only [hstop, bind_ok]
      simp [c1, c2, c3, kids, hhalf, hmid, hr, hc, collect_ok, node_ok _ _ _ _ width, value,
        outside o lp half s loc e (by omega) (Or.inl (by omega))]

/-- The honest root of a snapshot of height `h` holding `items`. -/
def honestRoot (items : Std.U64 → Slice Std.U8) (h : Nat) : Bytes :=
  rootTerm domain (pos (2 ^ h)) (tree items h (2 * (2 ^ h - 1)) 0)

/-- The honest siblings of `loc` in a snapshot of height `h`, as a slice. -/
def honestSiblings
    (items : Std.U64 → Slice Std.U8) (h : Nat) (loc : Std.U64)
    (bound : h ≤ maxHeight) :
    Slice Bytes :=
  Slice.from (path items h (2 * (2 ^ h - 1)) 0 loc.val)
    (by rw [path_length]; have top := maxHeight_eq; scalar_tac)

/-- On the honest siblings of an honest snapshot followed by `rest`, the extracted verifier
accepts exactly when `rest` is empty. -/
theorem honest_verify (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ maxHeight)
    (loc : Std.U64) (inside : loc.val < 2 ^ h.val) (ws : Slice Bytes) (rest : List Bytes)
    (siblings : ws.val = path items h.val (2 * (2 ^ h.val - 1)) 0 loc.val ++ rest) :
    qmdb.verify dyTerms () h loc (honestRoot items h.val) (items loc) ws =
      RustM.ok (decide (rest = [])) := by
  have top := maxHeight_eq
  have fits := maxLeaves_fits
  have small : 2 ^ h.val ≤ maxLeaves := leaves_le_maxLeaves bound
  have one : 1 ≤ 2 ^ h.val := Nat.one_le_two_pow
  obtain ⟨w, p, e, wv, pv, ev, run⟩ :=
    verify_eq h bound loc (honestRoot items h.val) (items loc) ws inside
  rw [run]
  have len : ws.val.length = h.val + rest.length := by simp [siblings, path_length]
  by_cases empty : rest = []
  · subst empty
    obtain ⟨r, hrun, re, -, rc⟩ := honest_rec items h.val p w 0#u64 loc e (start (items loc) ws)
      [] wv bound (by omega) (by simp; omega) (by simp) (by simp; omega) ev rfl
      (by simp [siblings, pv])
    have rooted : rootTerm domain w (tree items h.val p.val 0) = honestRoot items h.val := by
      have : w = pos (2 ^ h.val) := by rw [← wv, pos_val]
      simp [honestRoot, this, pv]
    simp only [len, List.length_nil, Nat.add_zero, ↓reduceIte, hrun, bind_ok]
    simp [verdict, re, rc, len, rooted]
  · have : ¬ ws.val.length = h.val := by
      have := List.length_pos_iff.mpr empty
      omega
    simp [this, empty]

/-- The extracted verifier accepts every honest opening of an honest snapshot.
-/
theorem honest_opening
    (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ maxHeight)
    (loc : Std.U64)
    (inside : loc.val < 2 ^ h.val) :
    qmdb.verify dyTerms () h loc (honestRoot items h.val) (items loc)
      (honestSiblings items h.val loc bound) =
      RustM.ok true := by
  simpa using honest_verify items h bound loc inside _ [] (by simp [honestSiblings])

/-- The extracted verifier rejects an honest opening followed by an unused
sibling. -/
theorem extra_sibling_rejected
    (items : Std.U64 → Slice Std.U8) (h : Std.U32)
    (bound : h.val ≤ maxHeight)
    (loc : Std.U64)
    (inside : loc.val < 2 ^ h.val)
    (ws : Slice Bytes) (extra : Bytes)
    (siblings :
      ws.val = path items h.val (2 * (2 ^ h.val - 1)) 0 loc.val ++ [extra]) :
    qmdb.verify dyTerms () h loc (honestRoot items h.val) (items loc) ws =
      RustM.ok false := by
  simpa using honest_verify items h bound loc inside ws [extra] siblings

/-! ## Totality -/

theorem sibling_total (o : Opening) : ∃ res r,
    traversal.Opening.Insts.Commonware_symbolicTraversalBackend.sibling mmr single element
      noCollect o = RustM.ok (res, r) := by
  by_cases room : o.cursor.val < o.siblings.length
  · obtain ⟨c, hc, -⟩ := sibling_ok o room
    exact ⟨_, _, hc⟩
  · exact ⟨_, _, sibling_end o room⟩

theorem leaf_total (o : Opening) (p : Std.U64) : ∃ res r,
    traversal.Opening.Insts.Commonware_symbolicTraversalBackend.leaf mmr single element noCollect
      o p = RustM.ok (res, r) := by
  cases h : o.elements with
  | some a => exact ⟨_, _, leaf_some o a h p⟩
  | none =>
    refine ⟨.Err .MissingElements, { o with elements := none }, ?_⟩
    simp [traversal.Opening.Insts.Commonware_symbolicTraversalBackend.leaf, h,
      reconstruct.Single.Insts.CoreIterTraitsIteratorIteratorElement.next]

/-- The production traversal returns, without panicking or diverging, on every subtree of an
MMR within the production size limit, whatever the siblings, elements and queried range. -/
theorem reconstruct_total (H : Nat) : ∀ (p w s loc e : Std.U64) (o : Opening),
    w.val = 2 ^ H → H ≤ maxHeight → 2 * (w.val - 1) ≤ p.val → s.val + w.val ≤ maxLeaves →
    ∃ res r, traversal.reconstruct backend o p w s loc e = RustM.ok (res, r) := by
  induction H with
  | zero =>
    intro p w s loc e o width _ _ bound
    simp at width
    by_cases off : s.val + w.val ≤ loc.val ∨ e.val ≤ s.val
    · rw [outside o p w s loc e bound off]
      exact sibling_total o
    rw [reconstruct_one o p w s loc e width (by omega) (by omega)]
    exact leaf_total o p
  | succ n ih =>
    intro p w s loc e o width bound position start
    have one : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have fits := maxLeaves_fits
    have double : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    by_cases off : s.val + w.val ≤ loc.val ∨ e.val ≤ s.val
    · rw [outside o p w s loc e start off]
      exact sibling_total o
    obtain ⟨stop, hstop, stopv⟩ := add_ok s w (by scalar_tac)
    have c1 : ¬ stop.val ≤ loc.val := by omega
    have c2 : ¬ e.val ≤ s.val := by omega
    have c3 : ¬ w.val = 1 := by omega
    obtain ⟨lp, rp, kids, lpv, rpv⟩ := children_ok p w (n + 1) width bound (by omega) (by omega)
    obtain ⟨half, hhalf, halfv⟩ := UScalar.div_spec w (y := 2#u64) (by decide)
    have halfv' : half.val = 2 ^ n := by simp at halfv; omega
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
      | Ok r => simp [c1, c2, c3, kids, hhalf, hmid, hl, hr, collect_ok, node_ok _ _ _ _ width]

/-- The extracted verifier returns a verdict, without panicking or diverging, on
every input. -/
theorem verify_total
    (h : Std.U32) (loc : Std.U64) (root : Bytes)
    (item : Slice Std.U8) (ws : Slice Bytes) :
    ∃ b, qmdb.verify dyTerms () h loc root item ws = RustM.ok b := by
  have top := maxHeight_eq
  have fits := maxLeaves_fits
  by_cases tall : h.val > maxHeight
  · have : h > qmdb.MAX_HEIGHT := (above_maxHeight h).mpr tall
    unfold qmdb.verify
    simp [this]
  by_cases out : 2 ^ h.val ≤ loc.val
  · exact ⟨false, verify_outside h (by omega) loc root item ws out⟩
  have small : 2 ^ h.val ≤ maxLeaves := leaves_le_maxLeaves (by omega)
  have one : 1 ≤ 2 ^ h.val := Nat.one_le_two_pow
  obtain ⟨w, p, e, wv, pv, ev, run⟩ := verify_eq h (by omega) loc root item ws (by omega)
  rw [run]
  split
  · obtain ⟨res, r, hr⟩ := reconstruct_total h.val p w 0#u64 loc e (start item ws) wv (by omega)
      (by omega) (by simp; omega)
    exact ⟨verdict w root ws res r, by rw [hr]; simp⟩
  · exact ⟨false, rfl⟩

end
end Qmdb.Verifier
