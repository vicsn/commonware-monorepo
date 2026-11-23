module
public import Qmdb.Ordered
public import Qmdb.Mmb
public import Qmdb.MmbHeader

/-! The correctly formed ordered database and its authenticated MMB header. -/

namespace Qmdb.Ordered
@[expose] public section

/-- An ordered journal and its corresponding public MMB header. -/
structure Database [LinearOrder K] (enc : Encoding K V) where
  /-- Well-formed logical journal. -/
  journal : Snapshot K V enc
  /-- Public header with the concrete dimension and suffix opening. -/
  header : Mmb.Header
  /-- The journal root matches the presented header. -/
  root_eq : journal.auth.root = header.root
  /-- Both describe the same number of leaves. -/
  count_eq : journal.auth.leaves = header.leaves.toNat
  /-- Both describe the pinned binary layout. -/
  layout : Mmb.Layout journal.auth header.inactive.toNat

end
end Qmdb.Ordered
