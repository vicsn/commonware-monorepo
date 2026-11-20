module
public import Commonware.Symbolic.Terms

/-! QMDB's term algebra and the input that the application supplies. Trusted. `#combine` fixes
DyLean's bytes to literals, concatenation and hashing, which the shared reading in
`Commonware.Symbolic.Terms` needs. `Snapshot` is the authenticated historical snapshot: its root
and the assumption that every stored item has an opening that the production verifier accepts
under it. -/

namespace Qmdb
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Literal,
  Concat,
  Hash,

/-- A fixed, authenticated historical snapshot with `2^height` leaves. The application supplies
its root, and every stored item has an opening that the production verifier accepts under it. -/
class Snapshot where
  height : Std.U32
  root : Bytes
  items : Std.U64 → Slice Std.U8
  honest : ∀ loc : Std.U64, loc.val < 2^height.val → ∃ ws : Slice Bytes,
    qmdb.verify dyTerms () height loc root (items loc) ws = RustM.ok true

end
end Qmdb
