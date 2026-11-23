module
public meta import Lean

/-! `#audit_axioms N₁ N₂ ...` checks every theorem in the namespaces `Nᵢ`: each may depend only on
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). A proof that skips a step
with `sorry`, evaluates natively or assumes an extra axiom fails the audit, and so does an axiom
declared in those namespaces. Run it in a module that imports every module of a target, so new
theorems are audited without being listed.

Imported theorems appear as axioms in the module system; `collectAxioms` still reads the axioms
that their proofs use from the exporting module. -/

public section
namespace Commonware.Symbolic
open Lean Elab Command

/-- The axioms that a checked theorem may depend on. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Audit every theorem in the given namespaces for non-standard axioms. -/
syntax (name := auditAxioms) "#audit_axioms" (ppSpace ident)+ : command

/-- Elaborate `#audit_axioms`: fail on every theorem or axiom of the given namespaces that
depends on a non-standard axiom. -/
@[command_elab auditAxioms] meta def elabAuditAxioms : CommandElab
  | `(#audit_axioms $namespaces*) => do
    let prefixes := namespaces.map (·.getId)
    let env ← getEnv
    let audited := env.constants.fold (init := #[]) fun found name info =>
      if (info matches .thmInfo _ || info matches .axiomInfo _) && !name.isInternalDetail &&
          prefixes.any (·.isPrefixOf name) then found.push name else found
    if audited.isEmpty then
      throwError "no theorems in {prefixes}"
    let mut failures : Array MessageData := #[]
    for name in audited.qsort Name.lt do
      let extra := (← liftCoreM (collectAxioms name)).filter (!standardAxioms.contains ·)
      unless extra.isEmpty do
        failures := failures.push m!"{name}: {extra}"
    unless failures.isEmpty do
      let listed := MessageData.joinSep failures.toList Format.line
      throwError "theorems with non-standard axioms:{indentD listed}"
    logInfo m!"{audited.size} theorems in {prefixes} depend only on standard axioms."
  | _ => throwUnsupportedSyntax

end Commonware.Symbolic
end
