module
public import Commonware.Symbolic.Signing

/-! A linear model of signatures with key aggregation, and its attacker. A key is a formal integer
combination of member secrets and a signature assigns to every hashed point the key it signs that
point under, so signatures add, subtract and scale as the attacker pleases. Members may register
any key, including one that depends on another member's, and several whose secrets sum to zero.
Hashing to points is any function, so it may collide.

Trusted: the definitions, which say what the attacker can derive and what the scheme accepts.
Checked: `attribution`, which reduces an accepted signature to a signing event of a protected
member or to an explicit collision of the hash. -/

namespace Commonware.Symbolic
@[expose] public section

/-- Two different inputs that a function maps to the same value. -/
def Collision {α β : Type} (hash : α → β) (x y : α) : Prop :=
  x ≠ y ∧ hash x = hash y

end
end Commonware.Symbolic

namespace Commonware.Symbolic.Linear
open Aeneas Aeneas.Std
@[expose] public section

/-- A key: a formal integer combination of the secrets of the members. -/
abbrev Key := Nat → Int

/-- The key of a member that registered its own secret. -/
def basis (member : Nat) : Key :=
  fun other => if other = member then 1 else 0

/-- What a signature covers: a message in a namespace, or the possession of a key. The two are
different inputs, as production separates them by domain tag. -/
inductive Input (B : Type) where
  | message (ns payload : B)
  | possession (key : Key)

variable {B P : Type}

/-- A signature: for every hashed point, the key that it signs the point under. -/
abbrev Sig (P : Type) := P → Key

/-- The signature of `point` under `key`. -/
noncomputable def term (key : Key) (point : P) : Sig P := by
  classical exact fun other => if other = point then key else fun _ => 0

/-- What the attacker can derive from the signing and compromise events so far: nothing, the
signatures that members issued, every member's proof of possession of its own key, anything
under a compromised member's key, and sums and integer multiples of those. -/
inductive Derives (hash : Input B → P) (signed : Nat → B → B → Prop) (leaked : Nat → Prop) :
    Sig P → Prop where
  | zero : Derives hash signed leaked (fun _ _ => 0)
  | sign {member : Nat} {ns payload : B} (event : signed member ns payload) :
      Derives hash signed leaked (term (basis member) (hash (.message ns payload)))
  | pop (member : Nat) :
      Derives hash signed leaked (term (basis member) (hash (.possession (basis member))))
  | corrupt {member : Nat} (event : leaked member) (point : P) :
      Derives hash signed leaked (term (basis member) point)
  | add {a b : Sig P} : Derives hash signed leaked a → Derives hash signed leaked b →
      Derives hash signed leaked (fun point member => a point member + b point member)
  | scale (factor : Int) {a : Sig P} : Derives hash signed leaked a →
      Derives hash signed leaked (fun point member => factor * a point member)

/-- What a member's own secret has been applied to: the messages it signed, and the possession
of its own key. -/
def Origin (signed : Nat → B → B → Prop) (member : Nat) : Input B → Prop
  | .message ns payload => signed member ns payload
  | .possession key => key = basis member

/-- A derived signature involves the secret of a member that is not compromised only at the hash
of something that member's secret was applied to. -/
theorem support {hash : Input B → P} {signed : Nat → B → B → Prop} {leaked : Nat → Prop}
    {s : Sig P} {member : Nat} (derived : Derives hash signed leaked s) (safe : ¬ leaked member)
    (point : P) (involved : s point member ≠ 0) :
    ∃ input, hash input = point ∧ Origin signed member input := by
  induction derived with
  | zero => exact absurd rfl involved
  | @sign signer ns payload event =>
    unfold term at involved
    split at involved
    · rename_i here
      unfold basis at involved
      split at involved
      · rename_i same
        exact ⟨.message ns payload, here.symm, same ▸ event⟩
      · exact absurd rfl involved
    · exact absurd rfl involved
  | pop signer =>
    unfold term at involved
    split at involved
    · rename_i here
      unfold basis at involved
      split at involved
      · rename_i same
        exact ⟨.possession (basis signer), here.symm, by rw [same]; rfl⟩
      · exact absurd rfl involved
    · exact absurd rfl involved
  | @corrupt signer event other =>
    unfold term at involved
    split at involved
    · unfold basis at involved
      split at involved
      · rename_i same
        exact absurd (same ▸ event) safe
      · exact absurd rfl involved
    · exact absurd rfl involved
  | @add a b _ _ first second =>
    by_cases none : a point member = 0
    · exact second (by
        intro zero
        exact involved (by show a point member + b point member = 0; omega))
    · exact first none
  | @scale factor a _ inner =>
    exact inner (by
      intro zero
      exact involved (by show factor * a point member = 0; simp [zero]))

/-! ## The scheme -/

/-- A hashed message or a signature. -/
inductive Point (P : Type) where
  | hashed (point : P)
  | signature (sig : Sig P)

/-- The sum of `keys` as integer combinations. -/
def total (keys : List Key) : Key :=
  fun member => (keys.map fun key => key member).sum

/-- The linear scheme over a hash to points: keys add as integer combinations, and a signature is
accepted for a hashed point under a key exactly when it is the signature of that point under that
key. -/
noncomputable def scheme (hash : Input (Slice Std.U8) → P) : Signing Key (Point P) where
  zero := fun _ => 0
  add sum key := fun member => sum member + key member
  hash ns payload := .hashed (hash (.message ns payload))
  check key hashed signature := by
    classical exact match hashed, signature with
    | .hashed point, .signature sig => decide (sig = term key point)
    | _, _ => false

theorem extend_eq (hash : Input (Slice Std.U8) → P) : ∀ (keys : List Key) (sum : Key),
    (scheme hash).extend sum keys = fun member => sum member + total keys member
  | [], sum => by simp [Signing.extend, total]
  | key :: keys, sum => by
    have rest := extend_eq hash keys ((scheme hash).add sum key)
    simp only [Signing.extend, List.foldl_cons] at rest ⊢
    rw [rest]
    funext member
    simp [scheme, total]
    omega

/-- The scheme sums keys as integer combinations. -/
theorem sum_eq (hash : Input (Slice Std.U8) → P) (keys : List Key) :
    (scheme hash).sum keys = total keys := by
  rw [Signing.sum, extend_eq]
  funext member
  simp [scheme]

/-- The scheme accepts a signature for a subject under a key exactly when it is the signature of
the subject's hash under that key. -/
theorem check_iff (hash : Input (Slice Std.U8) → P) (key : Key) (ns payload : Slice Std.U8)
    (point : Point P) :
    (scheme hash).check key ((scheme hash).hash ns payload) point = true ↔
      point = .signature (term key (hash (.message ns payload))) := by
  cases point with
  | hashed other => simp [scheme]
  | signature sig => simp [scheme]

/-! ## Attribution -/

/-- A member whose flag is set has its key among the selected keys. -/
theorem mem_selected {K : Type} {key : K} : ∀ (bits : List Bool) (keys : List K) (member : Nat),
    keys[member]? = some key → bits[member]? = some true → key ∈ selected bits keys
  | [], _, _, _, flag => by simp at flag
  | _ :: _, [], _, held, _ => by simp at held
  | bit :: bits, first :: keys, 0, held, flag => by
    simp at held flag
    subst held flag
    simp [selected]
  | bit :: bits, first :: keys, member + 1, held, flag => by
    have later := mem_selected bits keys member (by simpa using held) (by simpa using flag)
    cases bit <;> simp [selected, later]

/-- Every selected key is the key of a member whose flag is set. -/
theorem of_mem_selected {K : Type} {key : K} : ∀ (bits : List Bool) (keys : List K),
    key ∈ selected bits keys →
    ∃ member : Nat, keys[member]? = some key ∧ bits[member]? = some true
  | [], keys, mem => by cases keys <;> simp [selected] at mem
  | bit :: _, [], mem => by cases bit <;> simp [selected] at mem
  | true :: bits, first :: keys, mem => by
    simp only [selected, List.mem_cons] at mem
    rcases mem with rfl | later
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨member, held, flag⟩ := of_mem_selected bits keys later
      exact ⟨member + 1, by simpa using held, by simpa using flag⟩
  | false :: bits, first :: keys, mem => by
    obtain ⟨member, held, flag⟩ := of_mem_selected bits keys (by simpa [selected] using mem)
    exact ⟨member + 1, by simpa using held, by simpa using flag⟩

/-- The attacker can derive a signature under a sum of keys from signatures under each key. -/
theorem derives_total {hash : Input B → P} {signed : Nat → B → B → Prop} {leaked : Nat → Prop}
    (point : P) : ∀ keys : List Key,
    (∀ key ∈ keys, Derives hash signed leaked (term key point)) →
    Derives hash signed leaked (term (total keys) point)
  | [], _ => by
    have empty : term (total []) point = fun _ _ => 0 := by
      funext other member
      by_cases here : other = point
      · simp [term, here, total]
      · simp [term, here]
    rw [empty]
    exact Derives.zero
  | key :: keys, each => by
    have split : term (total (key :: keys)) point =
        fun other member => term key point other member + term (total keys) point other member := by
      funext other member
      by_cases here : other = point
      · simp [term, here, total]
      · simp [term, here]
    rw [split]
    exact Derives.add (each key (by simp))
      (derives_total point keys fun key mem => each key (List.mem_cons_of_mem _ mem))

/-- Keys that each involve a member's secret not at all or once, one of them once, sum to a key
that involves it. -/
theorem total_pos (member : Nat) : ∀ (keys : List Key),
    (∀ key ∈ keys, key member = 0 ∨ key member = 1) → (∃ key ∈ keys, key member = 1) →
    0 < total keys member
  | [], _, ⟨_, mem, _⟩ => by simp at mem
  | first :: keys, units, ⟨key, mem, once⟩ => by
    have nonneg : ∀ rest : List Key, (∀ key ∈ rest, key member = 0 ∨ key member = 1) →
        0 ≤ total rest member := by
      intro rest
      induction rest with
      | nil => intro _; simp [total]
      | cons head tail ih =>
        intro bounded
        have := ih (fun key mem => bounded key (List.mem_cons_of_mem _ mem))
        have := bounded head (by simp)
        simp only [total, List.map_cons, List.sum_cons] at *
        omega
    have rest := nonneg keys (fun key mem => units key (List.mem_cons_of_mem _ mem))
    have head := units first (by simp)
    simp only [total, List.map_cons, List.sum_cons] at *
    rcases List.mem_cons.mp mem with rfl | later
    · omega
    · have := total_pos member keys (fun key mem => units key (List.mem_cons_of_mem _ mem))
        ⟨key, later, once⟩
      simp only [total] at this
      omega

/-- Attribution up to an explicit collision. Take a committee in which `member` registered its
own key and is not compromised, flags that name it, a derivable proof of possession for every
named key, and a derivable signature that verifies for the subject under the sum of the named
keys. Then the member signed exactly that namespace and message, or the hash collides: two
different inputs have one point, the first something that the member's secret was applied to,
the second the subject or the possession of a named key. -/
theorem attribution (hash : Input B → P) {signed : Nat → B → B → Prop} {leaked : Nat → Prop}
    (keys : List Key) (bits : List Bool) (member : Nat) (ns payload : B) (s : Sig P)
    (canonical : keys[member]? = some (basis member)) (named : bits[member]? = some true)
    (pops : ∀ key ∈ selected bits keys,
      Derives hash signed leaked (term key (hash (.possession key))))
    (derived : Derives hash signed leaked s)
    (verified : s = term (total (selected bits keys)) (hash (.message ns payload)))
    (safe : ¬ leaked member) :
    signed member ns payload ∨ ∃ x y, Collision hash x y ∧ Origin signed member x ∧
      (y = .message ns payload ∨ ∃ key ∈ selected bits keys, y = .possession key) := by
  classical
  by_cases rogue : ∃ key ∈ selected bits keys, key member ≠ 0 ∧ key ≠ basis member
  · obtain ⟨key, mem, involved, other⟩ := rogue
    obtain ⟨input, same, origin⟩ := support (pops key mem) safe (hash (.possession key))
      (by simpa [term] using involved)
    refine Or.inr ⟨input, .possession key, ⟨?_, same⟩, origin, Or.inr ⟨key, mem, rfl⟩⟩
    intro here
    subst here
    exact other origin
  · have units : ∀ key ∈ selected bits keys, key member = 0 ∨ key member = 1 := by
      intro key mem
      by_cases none : key member = 0
      · exact Or.inl none
      · have own : key = basis member :=
          Classical.byContradiction fun other => rogue ⟨key, mem, none, other⟩
        exact Or.inr (by simp [own, basis])
    have positive := total_pos member (selected bits keys) units
      ⟨basis member, mem_selected bits keys member canonical named, by simp [basis]⟩
    obtain ⟨input, same, origin⟩ := support derived safe (hash (.message ns payload)) (by
      rw [verified]
      simp only [term, ite_true]
      omega)
    by_cases here : input = .message ns payload
    · subst here
      exact Or.inl origin
    · exact Or.inr ⟨input, .message ns payload, ⟨here, same⟩, origin, Or.inl rfl⟩

end
end Commonware.Symbolic.Linear
