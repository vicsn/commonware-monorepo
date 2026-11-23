module
public import Commonware.Symbolic.Terms

/-! QMDB's term algebra and the input that the application supplies. Trusted. `#combine` fixes
DyLean's bytes to literals, concatenation and hashing, which the shared reading in
`Commonware.Symbolic.Terms` needs. `Snapshot` is the authenticated historical snapshot: its root,
and the assumption that the siblings it supplies for every stored item make an opening that the
extracted verifier accepts under that root. -/

namespace Qmdb
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Literal,
  Concat,
  Hash,

/-- A fixed, authenticated historical snapshot with `2 ^ height` leaves. The
application supplies its root and, for every stored item, siblings that make an
opening which the extracted verifier accepts under that root. -/
class Snapshot where
  /-- The trusted height: the snapshot has `2 ^ height` leaves. -/
  height : Std.U32
  /-- The trusted root. -/
  root : Bytes
  /-- The item stored at each location. -/
  items : Std.U64 → Slice Std.U8
  /-- For each location, the siblings of an opening of its item. -/
  siblings : Std.U64 → Slice Bytes
  /-- The extracted verifier accepts that opening at every location. -/
  honest :
    ∀ loc : Std.U64,
      loc.val < 2 ^ height.val →
      qmdb.verify dyTerms () height loc root (items loc) (siblings loc) =
        RustM.ok true

end
end Qmdb
