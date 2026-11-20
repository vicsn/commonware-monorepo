module
import Commonware.Symbolic.Audit
import Bls.SecurityTheorems
import Bls.SanityChecks

/-! Every theorem of the BLS target and of the shared glue it uses depends only on Lean's standard
axioms. The build fails otherwise. -/

#audit_axioms Bls Commonware.Symbolic
