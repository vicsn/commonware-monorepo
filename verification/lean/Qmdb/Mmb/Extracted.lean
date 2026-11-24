module
public import Qmdb.Reconstruct
public import Qmdb.Mmb.Children
public import Qmdb.Mmb.Raw
public import Qmdb.Bitmap

/-! The extracted production verifier of a current operation proof over an MMB, related to the
hash-input program of `Plan`. Checked by Lean. -/

namespace Qmdb.Mmb.Extracted
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic Qmdb.Reconstruct
@[expose] public section

/-- The production MMB geometry. -/
abbrev mmbGeometry := geometry.Mmb.Insts.Commonware_symbolicReconstructGeometryPeaks

/-- The production read of the next MMB peak. -/
abbrev next := mmb_geometry.Peaks.Insts.Commonware_symbolicReconstructPeaks.next

/-! ## The peaks of an MMB -/

/-- The peaks that the iterator yields, as the reconstruction reads them. -/
theorem yields_of {it last : mmb_geometry.Peaks} {L : List (Nat × Nat)}
    (y : Peaks.Yields it L last) :
    ∃ L' : List (Std.U64 × Std.U32), Reconstruct.Yields next it L' ∧
      L'.map (fun q => (q.1.val, q.2.val)) = L := by
  induction y with
  | stop done =>
    exact ⟨[], .nil (by simpa [next,
      mmb_geometry.Peaks.Insts.Commonware_symbolicReconstructPeaks.next] using done), rfl⟩
  | step emit _ ih =>
    obtain ⟨L', y', m⟩ := ih
    exact ⟨_ :: L', .cons (by simpa [next,
      mmb_geometry.Peaks.Insts.Commonware_symbolicReconstructPeaks.next] using emit) y',
      by simp [m]⟩

theorem located_length (hs : List Nat) : ∀ start, (Peaks.located start hs).length = hs.length := by
  induction hs with
  | nil => intro; rfl
  | cons h hs ih => intro start; simp [Peaks.located, ih]

theorem located_heights (hs : List Nat) :
    ∀ start, (Peaks.located start hs).map Prod.snd = hs := by
  induction hs with
  | nil => intro; rfl
  | cons h hs ih => intro start; simp [Peaks.located, ih]

/-- The peak `containing` selects splits the located peaks around it. -/
theorem split_located (hs : List Nat) : ∀ (start i0 loc i h off : Nat),
    containing hs i0 loc = some (i, h, off) →
    ∃ pre post, Peaks.located start hs =
        pre ++ (subtreePosition (start + (loc - off)) h, h) :: post ∧
      pre.length + i0 = i ∧ (pre.map fun q => 2 ^ q.2).sum + off = loc ∧ off < 2 ^ h ∧
      pre.length + 1 + post.length = hs.length := by
  induction hs with
  | nil => intro start i0 loc i h off sel; simp [containing] at sel
  | cons h' rest ih =>
    intro start i0 loc i h off sel
    simp only [containing] at sel
    split at sel
    · rename_i here
      obtain ⟨rfl, rfl, rfl⟩ := sel
      refine ⟨[], Peaks.located (start + 2 ^ h') rest, by simp [Peaks.located], by simp,
        by simp, here, by simp [located_length]; omega⟩
    · rename_i past
      obtain ⟨pre, post, eq, len, sum, low, total⟩ := ih _ _ _ _ _ _ sel
      have within : off ≤ loc - 2 ^ h' := by omega
      refine ⟨(subtreePosition start h', h') :: pre, post, ?_, by simp; omega,
        by simp only [List.map_cons, List.sum_cons]; omega, low,
        by simp only [List.length_cons]; omega⟩
      rw [Peaks.located, eq]
      have same : start + 2 ^ h' + (loc - 2 ^ h' - off) = start + (loc - off) := by
        generalize 2 ^ h' = W at past within ⊢
        omega
      rw [same]
      rfl

theorem heights_sum (u : Nat) : ∀ k, ((peakHeights u k).map (2 ^ ·)).sum = leftWidth u k := by
  intro k
  induction k with
  | zero => simp [peakHeights, leftWidth, Nat.mod_one]
  | succ k ih => rw [peakHeights, List.map_cons, List.sum_cons, ih, width_step]

theorem heights_low (u : Nat) : ∀ k, ∀ h ∈ peakHeights u k, h ≤ k := by
  intro k
  induction k with
  | zero => simp [peakHeights]
  | succ k ih =>
    intro h mem
    simp only [peakHeights, List.mem_cons] at mem
    rcases mem with rfl | mem
    · simp only [peakHeight]; omega
    · exact (ih h mem).trans (by omega)

theorem heights_length (u : Nat) : ∀ k, (peakHeights u k).length = k := by
  intro k
  induction k <;> simp_all [peakHeights]

/-- The peaks of a valid MMB holding `loc`, as the reconstruction reads them: the ones before
the peak that holds it, that peak and the ones after. -/
theorem peaks_around (n : Std.U64) (valid : n.val ≤ Peaks.maxLeaves) {loc i h off : Nat}
    (sel : containing (heights n.val) 0 loc = some (i, h, off)) :
    ∃ (st : mmb_geometry.Peaks) (pre post : List (Std.U64 × Std.U32)) (pos : Std.U64)
      (hh : Std.U32),
      mmb_geometry.Peaks.new n = RustM.ok st ∧
      Reconstruct.Yields next st (pre ++ (pos, hh) :: post) ∧
      Low (pre ++ (pos, hh) :: post) ∧ span (pre ++ (pos, hh) :: post) = n.val ∧
      span pre + off = loc ∧ off < 2 ^ h ∧ pre.length = i ∧ hh.val = h ∧
      pos.val = subtreePosition (loc - off) h ∧
      pre.length + 1 + post.length = (heights n.val).length ∧
      (heights n.val).length ≤ 62 := by
  obtain ⟨init, last, new, -, ylds, -⟩ := Peaks.all_peaks n valid
  obtain ⟨L, ys, mapped⟩ := yields_of ylds
  obtain ⟨pre, post, eq, len, sum, low, total⟩ := split_located _ 0 0 loc i h off sel
  have logSmall : (n.val + 1).log2 ≤ 62 := Peaks.logBound (by omega)
  have count : (heights n.val).length ≤ 62 := by
    simp only [heights, heights_length]; exact logSmall
  rw [eq] at mapped
  obtain ⟨pre', rest', rfl, mpre, mrest⟩ := List.map_eq_append_iff.mp mapped
  obtain ⟨q, post', rfl, mq, mpost⟩ := List.map_eq_cons_iff.mp mrest
  obtain ⟨pos, hh⟩ := q
  simp only [Prod.mk.injEq] at mq
  obtain ⟨posv, hhv⟩ := mq
  have lenPre : pre'.length = pre.length := by rw [← mpre, List.length_map]
  have lenPost : post'.length = post.length := by rw [← mpost, List.length_map]
  have spanOf (xs : List (Std.U64 × Std.U32)) :
      span xs = ((xs.map (fun q => (q.1.val, q.2.val))).map fun q => 2 ^ q.2).sum := by
    simp [span, Function.comp_def]
  have lowAll : ∀ q ∈ Peaks.located 0 (heights n.val), q.2 ≤ 62 := by
    intro q mem
    have inH : q.2 ∈ heights n.val := by
      rw [← located_heights (heights n.val) 0]; exact List.mem_map_of_mem mem
    exact (heights_low _ _ _ inH).trans logSmall
  refine ⟨init, pre', post', pos, hh, new, ys, ?_, ?_, ?_, low, ?_, hhv, ?_, ?_, count⟩
  · intro q mem
    have : (q.1.val, q.2.val) ∈ Peaks.located 0 (heights n.val) := by
      rw [eq, ← mpre, ← mpost]
      simp only [List.mem_append, List.mem_cons, List.mem_map]
      rcases List.mem_append.mp mem with m | m
      · exact Or.inl ⟨q, m, rfl⟩
      · rcases List.mem_cons.mp m with rfl | m
        · exact Or.inr (Or.inl (by simp [posv, hhv]))
        · exact Or.inr (Or.inr ⟨q, m, rfl⟩)
    exact lowAll _ this
  · rw [spanOf, List.map_append, List.map_cons, mpre, mpost]
    have whole := heights_sum (n.val + 1) (n.val + 1).log2
    rw [width_all] at whole
    have mapH := located_heights (heights n.val) 0
    rw [eq] at mapH
    rw [← whole]
    simp only [heights] at mapH ⊢
    conv => rhs; rw [← mapH]
    simp [posv, hhv, Function.comp_def]
  · rw [spanOf, mpre]; omega
  · rw [lenPre]; simpa using len
  · rw [posv]; simp
  · rw [lenPre, lenPost]; exact total

/-! ## Rebuilding the peak that holds the location -/

/-- The eight-byte big-endian word of `Plan` is the bytes production hashes for a position. -/
theorem word_eq (p : Std.U64) : count (UInt64.ofNat p.val) = part (.Bytes (Verifier.be p)) := by
  rw [CurrentRoot.be_wire]
  simp only [count]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp

@[simp] theorem part_digest (d : Bytes) : part (.Digest d) = d := rfl

section Dfs
variable {N : Type} (nodes : traversal.Nodes N Bytes) (x : N) (raw : RawProof)
  (item : Slice Std.U8) (n : Nat) (g : Bool) (loc : Std.U64)

/-- An opening over `N` nodes with the one claimed item and no collector. -/
abbrev Opening := traversal.Opening N reconstruct.Single Unit Bytes

/-- The fields of `raw` with the claimed item as encoded bytes. -/
abbrev fields : Field → Bytes := raw.get (part (.Bytes item))

theorem sibling_ok (o : Opening (N := N)) (room : o.cursor.val < o.siblings.length) :
    ∃ c : Std.Usize, traversal.Opening.Insts.Commonware_symbolicTraversalBackend.sibling nodes
      single element noCollect o =
        RustM.ok (.Ok o.siblings.val[o.cursor.val], { o with cursor := c }) ∧
      c.val = o.cursor.val + 1 := by
  obtain ⟨c, hc, cv⟩ := succ_ok o.cursor o.siblings room
  refine ⟨c, ?_, cv⟩
  have roomv : o.cursor.val < o.siblings.val.length := room
  simp [traversal.Opening.Insts.Commonware_symbolicTraversalBackend.sibling,
    CoreModels.core.slice.Slice.get, roomv,
    CoreModels.core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    rust_primitives.slice.slice_length,
    rust_primitives.slice.slice_index, Verifier.index_ok o.siblings o.cursor room, hc]

/-- With enough siblings, the production traversal of an MMB subtree that holds `loc` returns
the value of `peakShape` over the proof's fields and reads exactly `k` siblings. The hypotheses
say how `nodes` lays out and hashes the subtrees on the path. -/
theorem dfs
    (childH : ∀ (s k : Nat) (p : Std.U64) (h : Std.U32), Peaks.Subtree n s (k + 1) →
      p.val = subtreePosition s (k + 1) → h.val = k + 1 →
      ∃ l r : Std.U64, nodes.children x p h = RustM.ok (l, r) ∧
        l.val = subtreePosition s k ∧ r.val = subtreePosition (s + 2 ^ k) k)
    (leafH : ∀ p a, nodes.leaf_digest x p a = RustM.ok (Verifier.leafTerm p a))
    (nodeH : ∀ (p : Std.U64) (h : Std.U32) (st : Std.U64) (l r : Bytes),
      st.val ≤ loc.val → loc.val < st.val + 2 ^ h.val → h.val ≤ 62 → 2 ^ h.val ∣ st.val →
      nodes.node_digest x p h st l r = RustM.ok
        (if g && h.val = 8 then Hash.hash (Concat.concat (Active.literal raw.chunk)
          (Verifier.nodeTerm p l r)) else Verifier.nodeTerm p l r)) (k : Nat) :
    ∀ (s : Nat) (p w st e : Std.U64) (o : Opening (N := N)),
      o.nodes = x → o.siblings.val = raw.digests → Peaks.Subtree n s k →
      p.val = subtreePosition s k → w.val = 2 ^ k → st.val = s → s ≤ loc.val →
      loc.val < s + 2 ^ k → e.val = loc.val + 1 → o.elements = .Some item →
      o.cursor.val + k ≤ raw.digests.length →
      ∃ c : Std.Usize, traversal.reconstruct (backend nodes) o p w st loc e =
        RustM.ok (.Ok ((peakShape g k s (loc.val - s) o.cursor.val).fill
          (fields raw item)).value, { o with elements := .None, cursor := c }) ∧
        c.val = o.cursor.val + k := by
  induction k with
  | zero =>
    intro s p w st e o hx hs tree hp hw hst lo hi he hel room
    refine ⟨o.cursor, ?_, rfl⟩
    obtain ⟨stop, hstop, stopv⟩ := add_ok st w (by scalar_tac)
    have c1 : ¬ stop.val ≤ loc.val := by simp at hw; omega
    have c2 : ¬ e.val ≤ st.val := by omega
    have c3 : w = 1#u64 := by scalar_tac
    have at_loc : loc.val - s = 0 := by simp at hi; omega
    rw [traversal.reconstruct.eq_def]
    simp only [hstop, bind_ok]
    simp [c1, c2, c3, traversal.Opening.Insts.Commonware_symbolicTraversalBackend.leaf, hel,
      reconstruct.Single.Insts.CoreIterTraitsIteratorIteratorElement.next,
      reconstruct.Element.Insts.CoreConvertAsRefSliceU8.as_ref, hx, leafH, peakShape,
      Shape.fill, Expr.value, RawProof.get, Verifier.leafTerm, chain, ← hp, word_eq]
  | succ k ih =>
    intro s p w st e o hx hs tree hp hw hst lo hi he hel room
    have one : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have double : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have valid := tree.valid
    have born := tree.born
    have hb := tree.heightBound
    have fits : s + 2 ^ (k + 1) ≤ n := by
      have := Peaks.birth_succ s k; simp only [Peaks.maxLeaves] at valid; omega
    have small : n < 2 ^ 63 := by simp only [Peaks.maxLeaves] at valid; omega
    obtain ⟨stop, hstop, stopv⟩ := add_ok st w (by scalar_tac)
    have c1 : ¬ stop.val ≤ loc.val := by omega
    have c2 : ¬ e.val ≤ st.val := by omega
    have c3 : ¬ w = 1#u64 := by
      intro h; have := congrArg UScalar.val h; simp at this; omega
    let hh : Std.U32 := ⟨BitVec.ofNat 32 (k + 1)⟩
    have hhv : hh.val = k + 1 := by
      change (BitVec.ofNat 32 (k + 1)).toNat = k + 1; simp; omega
    have ilog : CoreModels.core.num.U64.ilog2 w = RustM.ok hh := Verifier.ilog2_ok w (k + 1) hw
    obtain ⟨lp, rp, kids, lpv, rpv⟩ := childH s k p hh tree hp hhv
    obtain ⟨lt, rt⟩ := tree.children
    obtain ⟨half, hhalf, halfv⟩ := UScalar.div_spec w (y := 2#u64) (by decide)
    have halfv' : half.val = 2 ^ k := by simp at halfv; omega
    obtain ⟨mid, hmid, midv⟩ := add_ok st half (by scalar_tac)
    have midv' : mid.val = s + 2 ^ k := by omega
    have kidsB : traversal.Opening.Insts.Commonware_symbolicTraversalBackend.children nodes
        single element noCollect o p w = RustM.ok (lp, rp) := by
      simp [traversal.Opening.Insts.Commonware_symbolicTraversalBackend.children, ilog, hx,
        kids]
    have nodeB (c' : Std.Usize) (l r : Bytes) :
        traversal.Opening.Insts.Commonware_symbolicTraversalBackend.node nodes single element
          noCollect { o with elements := .None, cursor := c' } p w st l r = RustM.ok
          (if g && k + 1 = 8 then Hash.hash (Concat.concat (Active.literal raw.chunk)
            (Verifier.nodeTerm p l r)) else Verifier.nodeTerm p l r) := by
      simp only [traversal.Opening.Insts.Commonware_symbolicTraversalBackend.node, ilog,
        bind_ok, hx]
      rw [nodeH p hh st l r (by omega) (by rw [hhv]; omega) (by omega)
        (by rw [hhv, hst]; exact tree.aligned), hhv]
    have collectB (o' : Opening (N := N)) (lp rp : Std.U64) (l r : Bytes) :
        traversal.Opening.Insts.Commonware_symbolicTraversalBackend.collect nodes single element
          noCollect o' lp l rp r = RustM.ok o' := by
      simp [traversal.Opening.Insts.Commonware_symbolicTraversalBackend.collect,
        Tuple.Insts.Commonware_symbolicTraversalCollect.collect]
    rw [traversal.reconstruct.eq_def]
    simp only [hstop, bind_ok]
    by_cases side : loc.val < s + 2 ^ k
    · obtain ⟨c₁, left, c₁v⟩ := ih s lp half st e o hx hs lt lpv halfv' hst lo side he hel
        (by omega)
      have room₁ : c₁.val < raw.digests.length := by omega
      obtain ⟨c₂, hc₂, c₂v⟩ := sibling_ok nodes { o with elements := .None, cursor := c₁ }
        (by simp [Slice.length, hs]; omega)
      obtain ⟨stop₂, hstop₂, stop₂v⟩ := add_ok mid half (by scalar_tac)
      have out₂ : ¬ stop₂.val ≤ loc.val ∧ e.val ≤ mid.val := ⟨by omega, by omega⟩
      have right : traversal.reconstruct (backend nodes)
          { o with elements := .None, cursor := c₁ } rp half mid loc e =
          RustM.ok (.Ok raw.digests[c₁.val], { o with elements := .None, cursor := c₂ }) := by
        rw [traversal.reconstruct.eq_def]
        simp [hstop₂, out₂.2, hc₂, hs]
      refine ⟨c₂, ?_, by simp at c₂v; omega⟩
      simp [c1, c2, c3, kidsB, hhalf, hmid, left, right, collectB, nodeB]
      simp only [peakShape, show loc.val - s < 2 ^ k from by omega, ↓reduceIte, ← hp]
      have room₁' : o.cursor.val + k < raw.digests.length := by omega
      have get : (fields raw item) (.sibling (o.cursor.val + k)) = raw.digests[c₁.val] := by
        have same : raw.digests[c₁.val] = raw.digests[o.cursor.val + k] := by simp [c₁v]
        rw [same]
        simp [fields, RawProof.get, List.getElem?_eq_getElem room₁']
      cases g <;> by_cases hk : k = 7 <;>
        first
        | (subst hk; simp [Shape.fill, Expr.value, get, Verifier.nodeTerm, chain, word_eq,
            RawProof.get])
        | simp [hk, Shape.fill, Expr.value, get, Verifier.nodeTerm, chain, word_eq,
            RawProof.get]
    · have room₀ : o.cursor.val < raw.digests.length := by omega
      obtain ⟨c₁, hc₁, c₁v⟩ := sibling_ok nodes o (by simp [Slice.length, hs]; omega)
      obtain ⟨stop₁, hstop₁, stop₁v⟩ := add_ok st half (by scalar_tac)
      have out₁ : stop₁.val ≤ loc.val := by omega
      have left : traversal.reconstruct (backend nodes) o lp half st loc e =
          RustM.ok (.Ok raw.digests[o.cursor.val], { o with cursor := c₁ }) := by
        rw [traversal.reconstruct.eq_def]
        simp [hstop₁, out₁, hc₁, hs]
      obtain ⟨c₂, right, c₂v⟩ := ih (s + 2 ^ k) rp half mid e { o with cursor := c₁ } hx hs rt
        rpv halfv' midv' (by omega) (by omega) he hel (by simp; omega)
      refine ⟨c₂, ?_, by simp at c₂v; omega⟩
      simp [c1, c2, c3, kidsB, hhalf, hmid, left, right, collectB, nodeB]
      simp only [peakShape, show ¬ loc.val - s < 2 ^ k from by omega, ↓reduceIte, ← hp]
      have get : (fields raw item) (.sibling o.cursor.val) = raw.digests[o.cursor.val] := by
        simp [fields, RawProof.get, List.getElem?_eq_getElem room₀]
      cases g <;> by_cases hk : k = 7 <;>
        first
        | (subst hk; simp [Shape.fill, Expr.value, get, Verifier.nodeTerm, chain, word_eq,
            RawProof.get, c₁v, Nat.sub_add_eq])
        | simp [hk, Shape.fill, Expr.value, get, Verifier.nodeTerm, chain, word_eq,
            RawProof.get, c₁v, Nat.sub_add_eq]

end Dfs

/-! ## The nodes of a current proof -/

/-- The production MMB nodes, hashing with `dyTerms`. -/
abbrev mmbNodes :=
  reconstruct.StandardNodes.Insts.Commonware_symbolicTraversalNodes mmbGeometry dyTerms

/-- The nodes a current proof reconstructs over: the MMB nodes grafted with bitmap chunks. -/
abbrev GraftedNodes := grafting.Grafted (reconstruct.StandardNodes geometry.Mmb Unit) Unit
  current.Chunk

/-- The production grafting of the MMB nodes. -/
abbrev grafted := grafting.Grafted.Insts.Commonware_symbolicTraversalNodes mmbNodes dyTerms
  current.Chunk.Insts.CoreConvertAsRefSliceU8

theorem grafted_children (x : GraftedNodes) (n : Nat) (s k : Nat) (p : Std.U64) (h : Std.U32)
    (tree : Peaks.Subtree n s (k + 1)) (hp : p.val = subtreePosition s (k + 1))
    (hh : h.val = k + 1) :
    ∃ l r : Std.U64, grafted.children x p h = RustM.ok (l, r) ∧
      l.val = subtreePosition s k ∧ r.val = subtreePosition (s + 2 ^ k) k := by
  obtain ⟨l, r, ok, lv, rv, -, -⟩ := Peaks.physical_children tree p h hp hh
  refine ⟨l, r, ?_, lv, rv⟩
  simp [grafting.Grafted.Insts.Commonware_symbolicTraversalNodes.children,
    reconstruct.StandardNodes.Insts.Commonware_symbolicTraversalNodes.children,
    geometry.Mmb.Insts.Commonware_symbolicReconstructGeometryPeaks.children, ok]

theorem grafted_leaf (x : GraftedNodes) (p : Std.U64) (a : Slice Std.U8) :
    grafted.leaf_digest x p a = RustM.ok (Verifier.leafTerm p a) := by
  simp [grafting.Grafted.Insts.Commonware_symbolicTraversalNodes.leaf_digest,
    reconstruct.StandardNodes.Insts.Commonware_symbolicTraversalNodes.leaf_digest,
    Verifier.leaf_eq]

/-- `is_zero` from index `i` on: whether every later byte is zero. -/
theorem is_zero_loop_ok (c : Slice Std.U8) (k : Nat) : ∀ i : Std.Usize,
    c.val.length - i.val = k → i.val ≤ c.val.length →
    grafting.is_zero_loop c i =
      RustM.ok (decide (∀ j (hj : j < c.val.length), i.val ≤ j → c.val[j] = 0#u8)) := by
  induction k with
  | zero =>
    intro i hk hi
    have done : i.val = c.val.length := by omega
    have eq : i = Slice.len c := UScalar.eq_of_val_eq (by simp [done])
    have step : grafting.is_zero_loop.body c i = RustM.ok (.done true) := by
      simp [grafting.is_zero_loop.body, len_ok, eq]
    unfold grafting.is_zero_loop
    rw [loop_done _ _ _ step]
    have all : ∀ j (hj : j < c.val.length), i.val ≤ j → c.val[j] = 0#u8 :=
      fun j hj lo => absurd lo (by omega)
    simpa using all
  | succ k ih =>
    intro i hk hi
    have more : i.val < c.val.length := by omega
    have ne : ¬ i = Slice.len c := fun h => by
      have := congrArg UScalar.val h; simp at this; omega
    have get := Verifier.index_ok c i more
    by_cases zero : c.val[i.val] = 0#u8
    · obtain ⟨i₁, hi₁, i₁v⟩ := add_ok i 1#usize (by scalar_tac)
      have i₁v' : i₁.val = i.val + 1 := by simpa using i₁v
      have rest := ih i₁ (by omega) (by omega)
      have step : grafting.is_zero_loop.body c i = RustM.ok (.cont i₁) := by
        simp [grafting.is_zero_loop.body, len_ok, ne, get, zero, hi₁]
      unfold grafting.is_zero_loop at rest ⊢
      rw [loop_cont _ _ _ step, rest]
      congr 2
      apply propext
      constructor
      · intro all j hj lo
        by_cases at_i : j = i.val
        · subst at_i; exact zero
        · exact all j hj (by omega)
      · intro all j hj lo
        exact all j hj (by omega)
    · have zero' : ¬ (c.val[i.val]).val = 0 := fun h => zero (UScalar.eq_of_val_eq (by simp [h]))
      have step : grafting.is_zero_loop.body c i = RustM.ok (.done false) := by
        simp [grafting.is_zero_loop.body, len_ok, ne, get, zero']
      unfold grafting.is_zero_loop
      rw [loop_done _ _ _ step]
      congr 1
      simp only [Bool.false_eq, decide_eq_false_iff_not, not_forall]
      exact ⟨i.val, more, le_refl _, zero⟩

/-- A 32-byte chunk as the byte slice production reads. -/
abbrev chunkSlice (chunk : Active.Chunk) : Slice Std.U8 := Active.Chunk.asSlice chunk

theorem is_zero_ok (chunk : Active.Chunk) :
    grafting.is_zero (chunkSlice chunk) =
      RustM.ok (decide (chunk = Vector.replicate 32 0)) := by
  simp only [grafting.is_zero]
  rw [is_zero_loop_ok _ _ 0#usize rfl (by simp)]
  congr 1
  simp only [chunkSlice, Active.Chunk.asSlice, Slice.from_val, decide_eq_decide]
  constructor
  · intro all
    apply Vector.ext
    intro j hj
    have := all j (by simp; omega) (Nat.zero_le _)
    simp at this
    have v : (chunk[j]).toBitVec.toNat = 0 := congrArg UScalar.val this
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simpa using v
  · rintro rfl j hj -
    simp only [Vector.toList_replicate, List.map_replicate, List.getElem_replicate]
    rfl

/-- The chunk bytes as `Plan` reads them are the bytes production hashes. -/
theorem part_chunk (chunk : Active.Chunk) :
    part (.Bytes (chunkSlice chunk)) = Active.literal chunk := by
  simp only [part, Active.literal, chunkSlice, Active.Chunk.asSlice]
  congr 1
  apply ByteArray.ext
  have back (b : UInt8) : UInt8.ofNat (UScalar.val (⟨b.toBitVec⟩ : Std.U8)) = b := by
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp [UScalar.val]
  simp [toByteArray, Function.comp_def, back, Vector.toList]

/-- A node of the production grafted nodes over one chunk, on the path to `loc`: the plain MMB
node, or at height 8 the node grafted with the chunk when that chunk is graftable and nonzero. -/
theorem grafted_node (chunk : Active.Chunk) (chunks : Slice current.Chunk)
    (one : chunks.val = [chunkSlice chunk]) (startChunk graftable loc : Std.U64)
    (hsc : startChunk.val = loc.val / 256) (p : Std.U64) (h : Std.U32) (st : Std.U64)
    (l r : Bytes) (lo : st.val ≤ loc.val) (hi : loc.val < st.val + 2 ^ h.val) (low : h.val ≤ 62)
    (aligned : 2 ^ h.val ∣ st.val) :
    grafted.node_digest ⟨⟨(), ()⟩, (), 8#u32, startChunk, chunks, graftable⟩ p h st l r =
      RustM.ok (if (decide (loc.val / 256 < graftable.val) &&
          !decide (chunk = Vector.replicate 32 0)) && h.val = 8 then
        Hash.hash (Concat.concat (Active.literal chunk) (Verifier.nodeTerm p l r))
        else Verifier.nodeTerm p l r) := by
  have plain : reconstruct.StandardNodes.Insts.Commonware_symbolicTraversalNodes.node_digest
      mmbGeometry dyTerms ⟨(), ()⟩ p h st l r = RustM.ok (Verifier.nodeTerm p l r) := by
    simp [reconstruct.StandardNodes.Insts.Commonware_symbolicTraversalNodes.node_digest,
      Verifier.node_eq]
  by_cases eight : h = 8#u32
  case neg =>
    have ne : h.val ≠ 8 := fun e => eight (UScalar.eq_of_val_eq (by simp [e]))
    simp [grafting.Grafted.Insts.Commonware_symbolicTraversalNodes.node_digest, plain, eight, ne]
  subst eight
  have hv : (8#u32 : Std.U32).val = 8 := rfl
  rw [hv] at hi aligned
  obtain ⟨c, hc, cv, -, -⟩ := ok_of_partialSpec (UScalar.ShiftRight_spec st 8#u32)
    (by intro e; cases e <;> simp) (by simp)
  have cval : c.val = loc.val / 256 := by
    rw [cv, hv, Nat.shiftRight_eq_div_pow]
    obtain ⟨q, hq⟩ := aligned
    rw [hq] at lo hi ⊢
    simp at lo hi ⊢
    omega
  have cs : startChunk.val ≤ c.val := by omega
  by_cases late : loc.val / 256 < graftable.val
  case neg =>
    have over : graftable.val ≤ c.val := by omega
    simp [grafting.Grafted.Insts.Commonware_symbolicTraversalNodes.node_digest, plain,
      grafting.graft, hc, over, late]
  have under : ¬ graftable.val ≤ c.val := by omega
  have notBelow : ¬ c.val < startChunk.val := by omega
  obtain ⟨loc₀, hl, lv⟩ := sub_ok c startChunk (by omega)
  have zero₀ : loc₀.val = 0 := by omega
  have castZero : (UScalar.cast .Usize loc₀).val = 0 := by simp [zero₀]
  have get : Slice.index_usize chunks (UScalar.cast .Usize loc₀) = RustM.ok (chunkSlice chunk) := by
    rw [Verifier.index_ok chunks _ (by simp [castZero, Slice.length, one])]
    simp [castZero, one]
  by_cases nz : chunk = Vector.replicate 32 0
  · simp [grafting.Grafted.Insts.Commonware_symbolicTraversalNodes.node_digest, plain,
      grafting.graft, hc, under, notBelow, hl, len_ok, lift, one, zero₀, get,
      current.Chunk.Insts.CoreConvertAsRefSliceU8.as_ref, grafting.grafted_leaf, is_zero_ok,
      nz, late]
  · simp only [grafting.Grafted.Insts.Commonware_symbolicTraversalNodes.node_digest, plain,
      bind_ok]
    simp [grafting.graft, hc, under, notBelow, hl, len_ok, lift, one, zero₀, get,
      current.Chunk.Insts.CoreConvertAsRefSliceU8.as_ref, grafting.grafted_leaf, is_zero_ok,
      nz, late, CoreModels.core.array.Array.as_slice,
      CoreModels.rust_primitives.slice.array_as_slice, dyTerms, chain, part_chunk]

/-! ## Bagging the peaks -/

section Bag
variable (get : Field → Bytes)

/-- The value of a filled shape. -/
abbrev val (e : Shape) : Bytes := (e.fill get).value

theorem val_bag (x y : Shape) : val get (bag x y) = foldTerm (val get x) (val get y) := rfl

theorem val_foldl (L : List Shape) : ∀ a : Shape,
    val get (L.foldl bag a) = (L.map (val get)).foldl foldTerm (val get a) := by
  induction L with
  | nil => intro; rfl
  | cons x L ih => intro a; simp only [List.foldl_cons, List.map_cons, ih, val_bag]

theorem val_foldr (L : List Shape) (last : Shape) :
    val get (L.foldr bag last) = (L.map (val get)).foldr foldTerm (val get last) := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.foldr_cons, List.map_cons, val_bag, ih]

/-- `Plan`'s fold of a prefix then backward bagging is production's backward bagging. -/
theorem val_foldFrom (k : Nat) (first : Shape) (rest : List Shape) :
    val get (foldFrom k first rest) =
      bagWith foldTerm true k (val get first) (rest.map (val get)) := by
  unfold foldFrom bagWith
  simp only [← List.map_take, ← List.map_drop, ← List.map_reverse, ↓reduceIte]
  cases h : (rest.drop k).reverse with
  | nil => simp [val_foldl]
  | cons last rev =>
    simp only [List.map_cons, val_foldr, List.foldr_cons, val_bag, val_foldl, List.map_reverse]
    congr 1
    rw [List.foldr_reverse]

/-- The bag of `Plan`'s peak list. -/
theorem val_foldTarget (i inactive : Nat) (left : List Shape) (target : Shape)
    (right : List Shape) :
    ∃ first rest, (left ++ target :: right).map (val get) = first :: rest ∧
      val get (foldTarget i inactive left target right) =
        bagWith foldTerm true (toFoldOf true inactive i - 1) first rest := by
  have kept : (if min i inactive = 0 then inactive else inactive - min i inactive + 1) =
      toFoldOf true inactive i := by
    simp [toFoldOf, foldOf, Nat.min_comm]
  cases left with
  | nil =>
    refine ⟨val get target, right.map (val get), by simp, ?_⟩
    simp only [foldTarget, bagPeaks, kept, val_foldFrom]
  | cons l ls =>
    refine ⟨val get l, (ls ++ target :: right).map (val get), by simp, ?_⟩
    simp only [foldTarget, bagPeaks, kept, val_foldFrom]

end Bag

/-- The domain bytes production hashes into an MMB operations root are `Plan`'s. -/
theorem domain_eq :
    part (.Bytes (Aeneas.Std.Array.make 2#usize [mmb_geometry.DOMAIN, qmdb.BACKWARD_FOLD]).to_slice)
      = domainBytes := by
  simp only [part, domainBytes, wireLiteral]
  congr 1
  apply ByteArray.ext
  simp [toByteArray, Aeneas.Std.Array.make, Array.to_slice, mmb_geometry.DOMAIN,
    qmdb.BACKWARD_FOLD]

theorem be_same (x : Std.U64) : Reconstruct.be x = Verifier.be x := rfl

/-- `Plan`'s Merkle root is production's root over the same bag. -/
theorem val_merkle (get : Field → Bytes) (hd : get .domain = domainBytes)
    (hw : ∀ n, get (.word n) = count (UInt64.ofNat n)) (leaves : Std.U64) (inactive : Std.Usize)
    (folded : Shape) :
    val get (merkleShape leaves.val inactive.val folded) =
      rootTerm (Aeneas.Std.Array.make 2#usize [mmb_geometry.DOMAIN, qmdb.BACKWARD_FOLD])
        leaves (UScalar.cast .U64 inactive) (val get folded) := by
  have castv : (UScalar.cast .U64 inactive).val = inactive.val := by
    simp [UScalar.cast_val_eq]
    have b := UScalar.hBounds inactive
    have wide : 2 ^ System.Platform.numBits ≤ 2 ^ 64 :=
      Nat.pow_le_pow_right (by decide) (by cases System.Platform.numBits_eq <;> simp [*])
    simp only [UScalarTy.numBits] at b
    omega
  by_cases z : inactive.val = 0
  · have zc : UScalar.cast .U64 inactive = 0#u64 := UScalar.eq_of_val_eq (by simp [castv, z])
    simp [merkleShape, z, zc, rootTerm, val, Shape.fill, Expr.value, hd, hw, chain, domain_eq,
      word_eq, be_same]
  · have zc : ¬ UScalar.cast .U64 inactive = 0#u64 := fun e => z (by
      have := congrArg UScalar.val e; simp [castv] at this; exact this)
    have ws := word_eq (UScalar.cast .U64 inactive)
    rw [castv] at ws
    simp [merkleShape, z, zc, rootTerm, val, Shape.fill, Expr.value, hd, hw, chain, domain_eq,
      word_eq, ws, be_same]

/-! ## The checks of a current proof over one chunk -/

/-- A chunk of 32 bytes holds 256 bits. -/
theorem chunk_bits_ok : current.chunk_bits 32#usize = RustM.ok (.Some 256#u64) := by
  have wide : 2 ^ 32 ≤ 2 ^ System.Platform.numBits :=
    Nat.pow_le_pow_right (by decide) (by cases System.Platform.numBits_eq <;> simp [*])
  have maxv : (core.num.Usize.MAX).val = 2 ^ System.Platform.numBits - 1 := by
    simp [core.num.Usize.MAX, Usize.max, Usize.numBits]
  obtain ⟨q, hq, qv⟩ := UScalar.div_spec core.num.Usize.MAX (y := 8#usize) (by decide)
  have qbig : ¬ q.val < 32 := by rw [qv, maxv]; simp; omega
  obtain ⟨b, hb, bv⟩ := mul_ok (32#usize : Std.Usize) 8#usize (by scalar_tac)
  have cast : (UScalar.cast .U64 b) = 256#u64 := UScalar.eq_of_val_eq (by
    simp [UScalar.cast_val_eq] at bv ⊢; rw [bv])
  obtain ⟨m, hm, mv⟩ := sub_ok (256#u64 : Std.U64) 1#u64 (by decide)
  have bv' : b.val = 256 := by simpa using bv
  have mv' : m.val = 255 := by simpa using mv
  obtain ⟨top, ht, tv, -, -⟩ := ok_of_partialSpec (U64.ShiftLeft_IScalar_spec 1#u64 62#i32)
    (by intro e; cases e <;> simp) (by simp)
  have tv' : top.val = 2 ^ 62 := by
    rw [tv]; simp [U64.size, Nat.shiftLeft_eq, IScalar.toNat, U64.numBits]
  simp [current.chunk_bits, hq, hb, lift, cast, qbig, hm, ht, bv', mv', tv']

theorem chunk_len (chunk : Active.Chunk) : Slice.len (chunkSlice chunk) = 32#usize :=
  UScalar.eq_of_val_eq (by simp [chunkSlice, Active.Chunk.asSlice])

/-- The bitmap chunks of one chunk all have its size. -/
theorem sized_one (chunk : Active.Chunk) (chunks : Slice current.Chunk)
    (one : chunks.val = [chunkSlice chunk]) :
    current.sized current.Chunk.Insts.CoreConvertAsRefSliceU8 chunks 32#usize =
      RustM.ok true := by
  have lenOne : Slice.len chunks = 1#usize := UScalar.eq_of_val_eq (by simp [one])
  have ne : ¬ (0#usize : Std.Usize) = 1#usize := by decide
  have get := Verifier.index_ok chunks 0#usize (by simp [Slice.length, one])
  obtain ⟨i₁, hi₁, i₁v⟩ := add_ok (0#usize : Std.Usize) 1#usize (by scalar_tac)
  have i₁one : i₁ = 1#usize := UScalar.eq_of_val_eq (by simpa using i₁v)
  subst i₁one
  have size : (chunkSlice chunk).val.length = 32 := by simp [chunkSlice, Active.Chunk.asSlice]
  have step₀ : current.sized_loop.body current.Chunk.Insts.CoreConvertAsRefSliceU8 chunks
      32#usize 0#usize = RustM.ok (.cont 1#usize) := by
    simp [current.sized_loop.body, len_ok, lenOne, ne, get, one,
      current.Chunk.Insts.CoreConvertAsRefSliceU8.as_ref, size, hi₁]
  have step₁ : current.sized_loop.body current.Chunk.Insts.CoreConvertAsRefSliceU8 chunks
      32#usize 1#usize = RustM.ok (.done true) := by
    simp [current.sized_loop.body, len_ok, lenOne]
  simp only [current.sized, current.sized_loop]
  rw [loop_cont _ _ _ step₀, loop_done _ _ _ step₁]

/-- One chunk covers one operation exactly when the operation lies in the tree and below the
size bound. -/
theorem covered_one (chunk : Active.Chunk) (chunks : Slice current.Chunk)
    (one : chunks.val = [chunkSlice chunk]) (maxLeaves leaves loc : Std.U64)
    (positive : 1 ≤ maxLeaves.val) :
    current.covered current.Chunk.Insts.CoreConvertAsRefSliceU8 maxLeaves leaves loc 1#u64
      256#u64 chunks 32#usize =
      RustM.ok (decide (loc.val < maxLeaves.val ∧ loc.val < leaves.val)) := by
  have nz : ¬ (1#u64 : Std.U64) = 0#u64 := by decide
  have lenOne : Slice.len chunks = 1#usize := UScalar.eq_of_val_eq (by simp [one])
  have nonempty : CoreModels.core.slice.Slice.is_empty chunks = RustM.ok false := by
    simp [CoreModels.core.slice.Slice.is_empty, len_ok, lenOne]
  have fewer : ¬ (1#u64 : Std.U64) > maxLeaves := by scalar_tac
  obtain ⟨room, hroom, roomv⟩ := sub_ok maxLeaves 1#u64 (by simpa using positive)
  by_cases late : loc.val < maxLeaves.val
  case neg =>
    have past : room.val < loc.val := by simp at roomv; omega
    simp [current.covered, nz, nonempty, fewer, hroom, past, late]
  have before : ¬ room.val < loc.val := by simp at roomv; omega
  obtain ⟨e, he, ev⟩ := add_ok loc 1#u64 (by scalar_tac)
  by_cases inside : loc.val < leaves.val
  case neg =>
    have over : leaves.val < e.val := by simp at ev; omega
    simp [current.covered, nz, nonempty, fewer, hroom, he, over, inside]
  have notOver : ¬ leaves.val < e.val := by simp at ev; omega
  obtain ⟨l, hl, lv⟩ := sub_ok e 1#u64 (by simp at ev ⊢; omega)
  have lv' : l = loc := UScalar.eq_of_val_eq (by simp at ev lv; omega)
  subst lv'
  obtain ⟨q, hq, qv⟩ := UScalar.div_spec l (y := 256#u64) (by decide)
  obtain ⟨z, hz, zv⟩ := sub_ok q q (le_refl _)
  have zz : z.val = 0 := by rw [zv]; simp
  obtain ⟨o, ho, ov⟩ := add_ok z 1#u64 (by rw [zz]; simp [U64.max, U64.numBits])
  have ov' : o.val = 1 := by rw [ov, zz]; rfl
  simp [current.covered, nz, nonempty, fewer, hroom, before, he, notOver, hl, hq, hz, ho, len_ok,
    lenOne, lift, ov', sized_one chunk chunks one, late, inside]

/-- The leaf count at which an MMB's height-8 node first exists. -/
theorem birth_eight : mmbGeometry.birth_offset () 8#u32 = RustM.ok 383#u64 := by
  have z : ¬ (8#u32 : Std.U32) = 0#u32 := by decide
  obtain ⟨i, hi, iv⟩ := sub_ok (8#u32 : Std.U32) 1#u32 (by decide)
  have seven : i.val = 7 := by simpa using iv
  obtain ⟨half, hh, hv⟩ := pow_ok i (by omega)
  have halfv : half.val = 128 := by rw [hv, seven]; rfl
  have mul : CoreModels.core.num.U64.checked_mul half 3#u64 =
      RustM.ok (.Some ⟨BitVec.ofNat 64 384⟩) := by
    simp [CoreModels.core.num.U64.checked_mul, CoreModels.core.num.U64.overflowing_mul,
      rust_primitives.arithmetic.overflowing_mul_u64, uoverflowing_mul, halfv]
  obtain ⟨r, hr, rv⟩ := sub_ok (⟨BitVec.ofNat 64 384⟩ : Std.U64) 1#u64 (by decide)
  have r383 : r = 383#u64 := UScalar.eq_of_val_eq (by simp at rv; rw [rv]; decide)
  subst r383
  simp [geometry.Mmb.Insts.Commonware_symbolicReconstructGeometryPeaks.birth_offset,
    mmb_geometry.birth_offset, z, hi, seven, hh, mul, CoreModels.core.option.Option.expect, hr,
    massert, core.num.U64.BITS]

end
end Qmdb.Mmb.Extracted
