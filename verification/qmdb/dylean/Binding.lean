module
public import Model
namespace Qmdb
open DY

private theorem parts {a b c d : Bytes} (eq : Concat.concat a b = Concat.concat c d) :
    a = c ∧ b = d := by
  simp only [Concat.concat] at eq
  grind

private theorem subtree (items : Nat → ByteArray) (item : ByteArray)
    (h p start loc : Nat) (ws tail : List Bytes)
    (inside : start ≤ loc ∧ loc < start + 2^h)
    (ok : replay item h p start loc ws = some (tree items h p start, tail)) :
    item = items loc := by
  induction h generalizing p start ws tail with
  | zero =>
    have hl : loc = start := by simp at inside; omega
    subst loc
    simp [replay,tree] at ok
    have eq := (parts (Hash.hash_inj _ _ ok.1)).2
    simpa only [Literal.bytesToLiteral_literalToBytes, Option.some.injEq] using congrArg (Literal.bytesToLiteral (Bytes := Bytes)) eq
  | succ h ih =>
    simp only [replay] at ok
    split at ok
    · cases hr : replay item h (p-2^(h+1)) start loc ws with
      | none => simp [hr] at ok
      | some pair =>
        obtain ⟨l,rest⟩ := pair
        cases rest with
        | nil => simp [hr] at ok
        | cons r rest =>
          simp [hr,tree] at ok
          have eq := (parts (parts (Hash.hash_inj _ _ ok.1)).2).1
          exact ih _ _ _ _ (by omega) (eq ▸ hr)
    · cases ws with
      | nil => simp at ok
      | cons l rest =>
        cases hr : replay item h (p-1) (start+2^h) loc rest with
        | none => simp [hr] at ok
        | some pair =>
          obtain ⟨r,rem⟩ := pair
          simp [hr,tree] at ok
          have eq := (parts (parts (Hash.hash_inj _ _ ok.1)).2).2
          exact ih _ _ _ _ (by rw [Nat.pow_succ] at inside; omega) (eq ▸ hr)

public theorem inclusion_sound (items : Nat → ByteArray) (h loc : Nat)
    (item : ByteArray) (ws : List Bytes)
    (accepted : accepts h loc (wrap h (tree items h (2*(2^h-1)) 0)) item ws) :
    item = items loc := by
  obtain ⟨_,bound,peak,run,eq⟩ := accepted
  have peakEq := (parts (Hash.hash_inj _ _ eq)).2
  exact subtree items item _ _ _ _ _ _ (by omega) (peakEq ▸ run)

private theorem same_peak (a b : ByteArray) (h p start loc : Nat) (digest : Bytes)
    (sa sb ta tb : List Bytes)
    (ha : replay a h p start loc sa = some (digest,ta))
    (hb : replay b h p start loc sb = some (digest,tb)) : a = b := by
  induction h generalizing p start digest sa sb ta tb with
  | zero =>
    simp [replay] at ha hb
    have eq := (parts (Hash.hash_inj _ _ (ha.1.trans hb.1.symm))).2
    simpa only [Literal.bytesToLiteral_literalToBytes, Option.some.injEq] using
      congrArg (Literal.bytesToLiteral (Bytes := Bytes)) eq
  | succ h ih =>
    by_cases left : loc < start+2^h
    · simp only [replay,left,ite_true] at ha hb
      cases ea : replay a h (p-2^(h+1)) start loc sa with
      | none => simp [ea] at ha
      | some pa =>
        obtain ⟨x,rs⟩ := pa
        cases rs with
        | nil => simp [ea] at ha
        | cons r rest =>
          cases eb : replay b h (p-2^(h+1)) start loc sb with
          | none => simp [eb] at hb
          | some pb =>
            obtain ⟨y,ss⟩ := pb
            cases ss with
            | nil => simp [eb] at hb
            | cons t more =>
              simp [ea] at ha
              simp [eb] at hb
              have xy := (parts (parts (Hash.hash_inj _ _ (ha.1.trans hb.1.symm))).2).1
              exact ih _ _ _ _ _ _ _ (xy ▸ ea) eb
    · cases sa <;> cases sb <;> simp [replay,left] at ha hb
      next l xs r ys =>
        cases ea : replay a h (p-1) (start+2^h) loc xs with
        | none => simp [ea] at ha
        | some pa =>
          obtain ⟨x,rs⟩ := pa
          cases eb : replay b h (p-1) (start+2^h) loc ys with
          | none => simp [eb] at hb
          | some pb =>
            obtain ⟨y,ss⟩ := pb
            simp [ea] at ha
            simp [eb] at hb
            have xy := (parts (parts (Hash.hash_inj _ _ (ha.1.trans hb.1.symm))).2).2
            exact ih _ _ _ _ _ _ _ (xy ▸ ea) eb

public theorem fixed_root_binding (h loc : Nat) (root : Bytes) (a b : ByteArray)
    (sa sb : List Bytes) (ha : accepts h loc root a sa) (hb : accepts h loc root b sb) : a = b := by
  obtain ⟨_,_,x,ea,ra⟩ := ha
  obtain ⟨_,_,y,eb,rb⟩ := hb
  have eq := (parts (Hash.hash_inj _ _ (ra.trans rb.symm))).2
  exact same_peak _ _ _ _ _ _ _ _ _ _ _ (eq ▸ ea) eb

#print axioms fixed_root_binding

/-- Construct siblings in the verifier's DFS order, with an arbitrary unconsumed tail. -/
private def witness (items : Nat → ByteArray) : Nat → Nat → Nat → Nat → List Bytes → List Bytes
  | 0, _, _, _, tail => tail
  | h+1, p, start, loc, tail =>
    if loc < start+2^h then
      witness items h (p-2^(h+1)) start loc (tree items h (p-1) (start+2^h)::tail)
    else tree items h (p-2^(h+1)) start :: witness items h (p-1) (start+2^h) loc tail

private theorem honest (items : Nat → ByteArray) (h p start loc : Nat) (tail : List Bytes)
    (valid : start ≤ loc ∧ loc < start + 2^h) :
    replay (items loc) h p start loc (witness items h p start loc tail) =
      some (tree items h p start, tail) := by
  induction h generalizing p start tail with
  | zero =>
    have : loc = start := by simp at valid; omega
    simp [this, tree, replay, witness]
  | succ h ih =>
    by_cases left : loc < start + 2^h
    · simp [replay,witness,tree,left,ih _ start _ ⟨valid.1,left⟩]
    · have right : start+2^h ≤ loc ∧ loc < start+2^h+2^h := by
        rw [Nat.pow_succ] at valid; omega
      simp [replay,witness,tree,left,ih _ _ _ right]

public theorem honest_opening (items : Nat → ByteArray) (h loc : Nat)
    (bound : h ≤ 63) (inside : loc < 2^h) :
    ∃ ws, accepts h loc (wrap h (tree items h (2*(2^h-1)) 0)) (items loc) ws := by
  exact ⟨_,bound,inside,_,honest items h _ 0 loc [] (by omega),rfl⟩

#print axioms honest_opening
#print axioms inclusion_sound
end Qmdb
