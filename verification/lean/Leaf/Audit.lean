module
import Commonware.Symbolic.Audit
import Leaf.Protocol

/-! Every theorem of the leaf target and of the shared glue depends only on Lean's standard
axioms. The build fails otherwise. -/

#audit_axioms Leaf Commonware.Symbolic
