module
import Commonware.Symbolic.Audit
import Sake.Completeness
import Sake.SecurityTheorems

/-! Every theorem of the SAKE target and of the shared glue depends only on Lean's standard
axioms. The build fails otherwise. -/

#audit_axioms Sake Commonware.Symbolic
