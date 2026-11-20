module
public import Commonware.Symbolic.Terms

/-! QMDB's term algebra and the input that the application supplies. Trusted. `#combine` fixes
DyLean's bytes to literals, concatenation and hashing, which the shared reading in
`Commonware.Symbolic.Terms` needs. `Snapshot` is the authenticated historical snapshot: its hash,
which is any function on terms, its root, and the assumption that the siblings it supplies for
every stored item make an opening that the production verifier accepts under that root. -/

namespace Qmdb
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Literal,
  Concat,
  Hash,

/-- A fixed, authenticated historical snapshot with `2^height` leaves, under a hash on terms that
may collide. The application supplies its root and, for every stored item, siblings that make an
opening which the production verifier accepts under that root. -/
class Snapshot where
  hash : Bytes → Bytes
  height : Std.U32
  root : Bytes
  items : Std.U64 → Slice Std.U8
  siblings : Std.U64 → Slice Bytes
  honest : ∀ loc : Std.U64, loc.val < 2^height.val →
    qmdb.verify (hashing hash).terms () height loc root (items loc) (siblings loc) = RustM.ok true

/-- The snapshot's hash over DyLean's concatenation of the hash-input parts. -/
abbrev Snapshot.scheme [Snapshot] : Scheme Bytes Bytes := hashing Snapshot.hash

end
end Qmdb
