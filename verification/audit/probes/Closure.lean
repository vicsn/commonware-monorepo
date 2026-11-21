import Qmdb.SecurityTheorems
import Qmdb.SanityChecks
import Lean

/-! Which definitions the cited statements depend on, through definitions and not through proofs.
A probe of the first audit pass: what it lists under `Qmdb` and `Commonware` is the handwritten
Lean that a person must read, and no other handwritten Lean can change what a statement says. For
the generated extraction and for DyLean it prints counts. This file is not a module, so it sees
the bodies of every imported definition. Run it after check.sh, from `verification/lean`:

    lake env lean ../audit/probes/Closure.lean
-/

open Lean Elab Command

/-- What the meaning of a declaration depends on: its type, and its value unless it is a proof. -/
def meaningUses (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++ (match info with
    | .defnInfo d => d.value.getUsedConstants
    | .opaqueInfo d => d.value.getUsedConstants
    | .inductInfo d => d.ctors.toArray
    | _ => #[])

/-- Everything that the statements of `statements` mention. -/
def closure (env : Environment) (statements : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[]
  for statement in statements do
    if let some info := env.find? statement then
      todo := todo ++ info.type.getUsedConstants
  while !todo.isEmpty do
    let decl := todo.back!
    todo := todo.pop
    if seen.contains decl then continue
    seen := seen.insert decl
    if let some info := env.find? decl then
      todo := todo ++ meaningUses info
  return seen

def report (title : String) (statements : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  for statement in statements do
    unless env.contains statement do throwError "no such statement: {statement}"
  let mut handwritten : Std.HashMap Name (Array Name) := {}
  let mut others : Std.HashMap String Nat := {}
  for decl in (closure env statements).toArray.qsort Name.lt do
    let some index := env.getModuleIdxFor? decl | continue
    let file := env.header.moduleNames[index.toNat]!
    if (`Qmdb).isPrefixOf file || (`Commonware).isPrefixOf file then
      let shown := match env.find? decl with
        | some (.ctorInfo _) | some (.recInfo _) => false
        | _ => !decl.isInternalDetail
      if shown then
        handwritten := handwritten.insert file ((handwritten.getD file #[]).push decl)
    else
      let package := file.getRoot.toString
      others := others.insert package (others.getD package 0 + 1)
  IO.println s!"{title}"
  for (file, decls) in handwritten.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"  {file}: {String.intercalate ", " (decls.toList.map toString)}"
  IO.println s!"  other packages: {others.toArray.qsort (fun a b => a.1 < b.1)}"

run_cmd report "Byte-level statements" #[
  ``Qmdb.production_binding_or_collision, ``Qmdb.production_unique_or_collision]
run_cmd report "Symbolic statements without traces" #[
  ``Qmdb.production_binding, ``Qmdb.production_unique, ``Qmdb.honest_snapshots_exist]
run_cmd report "Statements that the report cites from the proof modules" #[
  ``Qmdb.Verifier.verify_total, ``Qmdb.Verifier.honest_opening,
  ``Qmdb.Verifier.extra_sibling_rejected, ``Qmdb.Symbolic.client_step_sound]
run_cmd report "Trace statements" #[
  ``Qmdb.extracted_client_authentication, ``Qmdb.collision_free_client_authentication]
