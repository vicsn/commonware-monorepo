module
public import QmdbTraversal.Extraction
public import Binding

namespace Qmdb.Bridge
open Aeneas CoreModels DY
open Aeneas.Std hiding namespace core alloc
open qmdb_traversal RustM
@[expose] public section

abbrev Stream := List DY.Bytes
abbrev Reply := RustM ((CoreModels.core.result.Result DY.Bytes qmdb_traversal.Error) × Stream)

def symbolic (item : ByteArray) : Backend Stream DY.Bytes where
  coremarkerCopyInst := ⟨⟨ok, fun _ x => ok x⟩⟩
  children := fun _ p w => do
    let l ← p - w
    let r ← p - 1#u64
    ok (l,r)
  sibling := fun
    | x :: xs => ok (.Ok x,xs)
    | [] => ok (.Err .MissingDigests,[])
  leaf := fun ws p => ok (.Ok (leaf p.val item),ws)
  node := fun _ p l r => ok (node p.val l r)
  collect := fun ws _ _ _ _ => ok ws

def reply : Option (DY.Bytes × Stream) → Reply
  | some (x,ws) => ok (.Ok x,ws)
  | none => ok (.Err .MissingDigests,[])

private theorem add_ok (x y : U64) (bound : x.val+y.val < 2^64) :
    ∃ z, x+y = ok z ∧ z.val = x.val+y.val := by
  have eq := UScalar.add_equiv x y
  cases hx : x+y with
  | ret z => exact ⟨z,rfl,by rw [hx] at eq; simpa using eq.2.1⟩
  | div => simp [hx] at eq
  | vis eff k => cases eff; simp [hx,UScalar.inBounds] at eq; omega

private theorem sub_ok (x y : U64) (bound : y.val ≤ x.val) :
    ∃ z, x-y = ok z ∧ z.val = x.val-y.val := by
  have eq := UScalar.sub_equiv x y
  cases hx : x-y with
  | ret z => refine ⟨z,rfl,?_⟩; rw [hx] at eq; simp at eq; omega
  | div => simp [hx] at eq
  | vis eff k => cases eff; simp [hx] at eq; omega

private theorem outside (item : ByteArray) (p w s loc e : U64) (ws : Stream)
    (bound : s.val + w.val < 2^64)
    (off : s.val + w.val ≤ loc.val ∨ e.val ≤ s.val) :
    reconstruct (symbolic item) ws p w s loc e = (symbolic item).sibling ws := by
  obtain ⟨stop,hs,hv⟩ := add_ok s w bound
  rw [reconstruct.eq_def,hs]
  simp only [bind_ok]
  split <;> first | rfl | split <;> first | rfl | scalar_tac

/-- All sibling streams, including short streams and streams with an unused suffix. -/
theorem replay_eq (item : ByteArray) (h : Nat) (p w s loc e : U64) (ws : Stream)
    (width : w.val = 2^h) (position : 2*(w.val-1) ≤ p.val)
    (bound : s.val + w.val < 2^64)
    (inside : s.val ≤ loc.val ∧ loc.val < s.val+w.val) (finish : e.val = loc.val+1) :
    reconstruct (symbolic item) ws p w s loc e =
      reply (replay item h p.val s.val loc.val ws) := by
  induction h generalizing p w s ws with
  | zero | succ h ih =>
    obtain ⟨stop,hs,hv⟩ := add_ok s w bound
    rw [reconstruct.eq_def,hs]
    have hstop : ¬stop ≤ loc := by scalar_tac
    have hstart : ¬s ≥ e := by scalar_tac
    simp only [bind_ok,hstop,hstart,ite_false]
    first
    | have one : w = 1#u64 := by scalar_tac
      simp [one,symbolic,replay,reply]
    | rw [Nat.pow_succ] at width
      have two : w ≠ 1#u64 := by scalar_tac
      obtain ⟨lp,hl,hlv⟩ := sub_ok p w (by omega)
      obtain ⟨rp,hr,hrv⟩ := sub_ok p 1#u64 (by scalar_tac)
      obtain ⟨half,hh,hhv⟩ := UScalar.div_spec w (y:=2#u64) (by decide)
      have hw : half.val = 2^h := by simp at hhv; omega
      obtain ⟨mid,hm,hmv⟩ := add_ok s half (by omega)
      have children : (symbolic item).children ws p w = ok (lp,rp) := by simp [symbolic,hl,hr]
      simp only [two,ite_false,children,bind_ok,hh,hm]
      simp at hrv
      change Aeneas.Std.bind (reconstruct (symbolic item) ws lp half s loc e) _ = _
      by_cases left : loc.val < s.val+2^h
      · have run := ih lp half s ws hw (by omega) (by omega) (by omega)
        have skip := fun xs => outside item rp half mid loc e xs (by omega) (by omega)
        simp only [replay,left,ite_true]
        simp only [run]
        rw [hlv,width,← Nat.pow_succ]
        cases c : replay item h (p.val-2^(h+1)) s.val loc.val ws with
        | none => simp [reply,bind_ok]
        | some pair =>
          obtain ⟨l,rest⟩ := pair
          simp only [reply,bind_ok]
          change Aeneas.Std.bind (reconstruct (symbolic item) rest rp half mid loc e) _ = _
          rw [skip]
          cases rest <;> simp [symbolic]
      · have skip := outside item lp half s loc e ws (by omega) (by omega)
        simp only [replay,left,ite_false,skip]
        cases ws with
        | nil => simp [symbolic,bind_ok]; rfl
        | cons l rest =>
          have run := ih rp half mid rest hw (by omega) (by omega) (by omega)
          have get : (symbolic item).sibling (l::rest) = ok (.Ok l,rest) := rfl
          rw [get]
          simp only [bind_ok]
          change Aeneas.Std.bind (reconstruct (symbolic item) rest rp half mid loc e) _ = _
          rw [run,hrv,hmv,hw]
          cases c : replay item h (p.val-1) (s.val+2^h) loc.val rest with
          | none => simp [reply]
          | some pair => cases pair; simp [reply,symbolic]
/-- The harness checks the model's wrapper and requires complete sibling consumption. -/
def verify (h loc : Nat) (root : DY.Bytes) (item : ByteArray) (ws : Stream) : Bool :=
  if bounded : h ≤ 63 then
    if valid : loc < 2^h then
      have limit : 2^h ≤ 2^63 := Nat.pow_le_pow_right (by decide) bounded
      let width := U64.ofNat (2^h) (by change _ ≤ 18446744073709551615; omega)
      let pos := U64.ofNat (2*(2^h-1)) (by change _ ≤ 18446744073709551615; omega)
      let query := U64.ofNat loc (by change _ ≤ 18446744073709551615; omega)
      let stop := U64.ofNat (loc+1) (by change _ ≤ 18446744073709551615; omega)
      match (reconstruct (symbolic item) ws pos width 0#u64 query stop).match with
      | .ok (.Ok peak,[]) => decide (wrap h peak = root)
      | _ => false
    else false
  else false

theorem verify_iff (h loc : Nat) (root : DY.Bytes) (item : ByteArray) (ws : Stream) :
    verify h loc root item ws = true ↔ accepts h loc root item ws := by
  unfold verify accepts
  split <;> rename_i bounded
  · split <;> rename_i valid
    · dsimp only
      rw [replay_eq item h _ _ _ _ _ ws (by scalar_tac) (by scalar_tac) (by
        have limit : 2^h ≤ 2^63 := Nat.pow_le_pow_right (by decide) bounded
        scalar_tac) (by scalar_tac) (by scalar_tac)]
      simp [bounded,valid,U64.ofNat] -- normalize the bounded machine integers
      cases hr : replay item h (2*(2^h-1)) 0 loc ws with
      | none => simp [reply]
      | some pair => obtain ⟨p,rest⟩ := pair; cases rest <;> simp [reply]
    · simp [valid]
  · simp [bounded]

#print axioms replay_eq
#print axioms verify_iff
end
end Qmdb.Bridge
