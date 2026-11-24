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
      st.val ≤ loc.val → loc.val < st.val + 2 ^ h.val → h.val ≤ 62 →
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
      rw [nodeH p hh st l r (by omega) (by rw [hhv]; omega) (by omega), hhv]
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

end
end Qmdb.Mmb.Extracted
