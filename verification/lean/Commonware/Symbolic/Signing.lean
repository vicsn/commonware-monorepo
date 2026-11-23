module
public import CommonwareSymbolic.Extraction
public import Commonware.Symbolic.RustM

/-! Trusted reading of the extracted production certificate rules for an arbitrary signature
scheme with key aggregation. A `Signing` is any choice of key sum, message hash and signature
check, and `Signing.terms` is the `Terms` implementation that runs them, so statements about the
rules hold whatever the scheme does. `Roster`, `Flags` and `decoded` read the committee, the
signer flags and the lazily decoded signature that the rules take. -/

namespace Commonware.Symbolic
open Aeneas Aeneas.Std CoreModels commonware_symbolic
@[expose] public section

/-- A signature scheme with key aggregation: public keys `K` with a sum, and points `P` that are
hashed messages or signatures. `hash` reads a namespace and a message; `hash` and `check` are any
functions. -/
structure Signing (K P : Type) where
  /-- The sum of no keys. -/
  zero : K
  /-- The sum of two keys. -/
  add : K → K → K
  /-- The point that a message hashes to in a namespace. -/
  hash : Slice Std.U8 → Slice Std.U8 → P
  /-- Whether a signature verifies under a key for a hashed message. -/
  check : K → P → P → Bool

variable {K P : Type}

/-- The `Terms` implementation of a scheme. -/
def Signing.terms (S : Signing K P) : rules.Terms Unit K P where
  zero _ := RustM.ok S.zero
  add _ sum key := RustM.ok (S.add sum key)
  message _ ns message := RustM.ok (S.hash ns message)
  check _ key hashed signature := RustM.ok (S.check key hashed signature)

/-- `keys` added to `sum` in order. -/
def Signing.extend (S : Signing K P) (sum : K) (keys : List K) : K :=
  keys.foldl S.add sum

/-- The sum of `keys`, added in order. -/
def Signing.sum (S : Signing K P) (keys : List K) : K :=
  S.extend S.zero keys

/-- An ordered committee: the keys of its members by index, and the quorum it asks for. -/
structure Roster (K : Type) where
  /-- The key of every member, by index. -/
  keys : List K
  /-- The quorum that the committee asks for. -/
  quorum : Std.U64
  /-- The number of members fits a `u64`. -/
  bounded : keys.length < 2 ^ 64

/-- Number of members. -/
def Roster.members (r : Roster K) : Std.U64 :=
  Std.U64.ofNatCore r.keys.length r.bounded

/-- The `Committee` implementation of a roster. -/
def Roster.committee : rules.Committee (Roster K) K where
  members r := RustM.ok r.members
  quorum r := RustM.ok r.quorum
  key r index := RustM.ok r.keys[index.val]?

/-- The signer flags of a certificate, one per index. -/
structure Flags where
  /-- Whether each index is named as a signer. -/
  bits : List Bool
  /-- The number of flags fits a `u64`. -/
  bounded : bits.length < 2 ^ 64

/-- Number of indices that the flags can name. -/
def Flags.bound (f : Flags) : Std.U64 :=
  Std.U64.ofNatCore f.bits.length f.bounded

/-- The `Signers` implementation of signer flags. Asking for an index without a flag fails, as
the production bitmap does. -/
def Flags.signers : rules.Signers Flags where
  bound f := RustM.ok f.bound
  names f index :=
    match f.bits[index.val]? with
    | some bit => RustM.ok bit
    | none => RustM.fail .panic

/-- A signature that decoded, or none. -/
def decoded : rules.Decoded (Option P) P where
  decoded signature := RustM.ok signature

/-- What a committee implementation says about one committee: its size, the quorum it asks for
and the key of every index. -/
structure Reads {C : Type} (inst : rules.Committee C K) (committee : C) (keys : List K)
    (quorum : Std.U64) : Prop where
  /-- The committee reports as many members as there are keys. -/
  members : ∃ members, inst.members committee = RustM.ok members ∧ members.val = keys.length
  /-- The committee reports this quorum. -/
  quorum : inst.quorum committee = RustM.ok quorum
  /-- The committee reports the key at every index, and none beyond the last. -/
  key : ∀ index : Std.U64, inst.key committee index = RustM.ok keys[index.val]?

theorem Roster.members_val (r : Roster K) : r.members.val = r.keys.length := by
  simp [Roster.members, U64.ofNatCore]

theorem Flags.bound_val (f : Flags) : f.bound.val = f.bits.length := by
  simp [Flags.bound, U64.ofNatCore]

theorem Roster.reads (r : Roster K) : Reads Roster.committee r r.keys r.quorum where
  members := ⟨r.members, rfl, r.members_val⟩
  quorum := rfl
  key _ := rfl

/-- The keys of the members that `bits` names, in index order. -/
def selected : List Bool → List K → List K
  | true :: bits, key :: keys => key :: selected bits keys
  | false :: bits, _ :: keys => selected bits keys
  | _, _ => []

/-- The indices that `bits` names, in ascending order from `first`. -/
def namedFrom : Nat → List Bool → List Nat
  | _, [] => []
  | first, true :: bits => first :: namedFrom (first + 1) bits
  | first, false :: bits => namedFrom (first + 1) bits

/-- The indices that `bits` names, in ascending order. -/
abbrev named (bits : List Bool) : List Nat :=
  namedFrom 0 bits

end
end Commonware.Symbolic
