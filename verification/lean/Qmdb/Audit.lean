module
import Commonware.Symbolic.Audit
import Qmdb.SecurityTheorems
import Qmdb.SanityChecks

/-! Every theorem of the QMDB target and of the shared glue depends only on Lean's standard
axioms. The build fails otherwise. -/

#audit_axioms Qmdb Commonware.Symbolic
