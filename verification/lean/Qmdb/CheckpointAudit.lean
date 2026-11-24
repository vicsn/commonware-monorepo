module
import Commonware.Symbolic.Audit
import Commonware.Symbolic.RootPair
import Qmdb.Bitmap
import Qmdb.Mmb.Children
import Qmdb.Mmb.RawHeader
import Qmdb.Mmb.Extracted
import Qmdb.Ordered.Encoding
import Qmdb.Ordered.Verified
import Qmdb.Ordered.Examples

/-! Audit the checkpoint reader's operation proofs, journal semantics, examples and hash model. -/

#audit_axioms Qmdb.Active Qmdb.CurrentRoot Qmdb.Mmb Qmdb.Ordered Commonware.Symbolic
