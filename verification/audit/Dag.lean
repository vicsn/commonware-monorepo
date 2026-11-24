import Qmdb.SecurityTheorems
import Qmdb.SanityChecks
import Commonware.Symbolic.RootPair
import Qmdb.Bitmap
import Qmdb.Mmb.Children
import Qmdb.Mmb.RawHeader
import Qmdb.Mmb.Extracted
import Qmdb.Ordered.Encoding
import Qmdb.Ordered.Verified
import Qmdb.Ordered.Examples
import Lean

/-! Every Lean declaration of the QMDB target with what it depends on, as JSON for the audit guide.
The target has two parts: single-item inclusion, and ordered reads under a checkpoint root in the
format of Commonware `v2026.11.0`. The imports after the first two are those of
`Qmdb.CheckpointAudit`.

A node is one declaration of the handwritten Lean, one generated definition that the handwritten
Lean reaches, or one library that both rest on. Lean derives helper constants for a declaration
(projections, matchers, proof terms, instances of a `#combine`); they belong to the node of the
source line that produced them. An edge says that a node mentions another. It is a `meaning` edge
when the statement of a theorem or the body of a definition mentions it, and a `proof` edge when
only the proof of a theorem does.

The trust type of a node follows from the edges. The statements that the guide cites are listed
below. Whatever they reach through meaning edges is what they say, so a person must read it: it
is `trusted` when handwritten, `generated` when hax produced it from the crate, and `assumed`
when it is a library. Every other handwritten declaration is `checked`: Lean accepts it, and no
statement depends on what it says. This file is not a module, so it sees the bodies of every imported
definition. `python3 verification/audit/build.py --dag` runs it and stores what it prints. -/

open Lean Elab Command

/-- The statements that the guide cites: those behind the README's sentences about inclusion,
those about ordered reads in the Lean model, and those that relate the model to extracted Rust.
`pairs.toml` names the same statements with the sentence that each backs. -/
def cited : Array Name := #[
  ``Qmdb.Verifier.unique, ``Qmdb.Verifier.verify_total, ``Qmdb.Verifier.verify_bounds,
  ``Qmdb.Verifier.honest_opening, ``Qmdb.Verifier.extra_sibling_rejected,
  ``Qmdb.honest_snapshots_exist, ``Qmdb.client_authentication,
  ``Qmdb.honest_acceptance_logged,
  -- Ordered reads in the model.
  ``Qmdb.Active.accepted, ``Qmdb.Active.honest, ``Qmdb.Mmb.RawProof.sound,
  ``Qmdb.Mmb.plan_coverage, ``Qmdb.Mmb.accepted, ``Qmdb.Mmb.honest,
  ``Qmdb.Mmb.RawProof.header_of_verify, ``Qmdb.Mmb.Header.binding,
  ``Qmdb.Ordered.accepted_read, ``Qmdb.Ordered.honest_member, ``Qmdb.Ordered.honest_gap,
  ``Qmdb.Ordered.honest_empty, ``Qmdb.Ordered.Layout.encode_ok,
  ``Qmdb.Ordered.Layout.bytes_inj, ``Qmdb.Ordered.Verified.verify_selected_sound,
  ``Commonware.Symbolic.rootPair_binding, ``Qmdb.Ordered.Examples.empty_claim,
  ``Qmdb.Ordered.Examples.singleton_claims,
  -- The model against extracted Rust.
  ``Qmdb.Ordered.Extraction.accepts_iff, ``Qmdb.Active.rustActive_eq,
  ``Qmdb.CurrentRoot.extracted_wire, ``Qmdb.Mmb.Extracted.verify_operation_refines,
  ``Qmdb.Mmb.Extracted.verify_operation_sound, ``Qmdb.Mmb.Extracted.verify_operation_header,
  ``Qmdb.Mmb.Extracted.dfs, ``Qmdb.Mmb.Extracted.grafted_node,
  ``Qmdb.Mmb.Peaks.all_peaks, ``Qmdb.Mmb.Peaks.physical_children]

/-- Where a constant is drawn: a source line of a file of this repository, or a library. -/
inductive Place where
  | line (file : Name) (row : Nat)
  | library (title : String)
  | nowhere
  deriving BEq, Hashable

def Place.key : Place → String
  | .line file row => s!"{file}:{row}"
  | .library title => title
  | .nowhere => ""

def fileOf (env : Environment) (decl : Name) : Option Name :=
  (env.getModuleIdxFor? decl).map fun index => env.header.moduleNames[index.toNat]!

def handwritten (file : Name) : Bool :=
  (`Qmdb).isPrefixOf file || (`Commonware).isPrefixOf file

def generated (file : Name) : Bool := (`CommonwareSymbolic).isPrefixOf file

/-- The declaration that a person or hax wrote and that produced `decl`: the type of a constructor
or of a field, the declaration that a helper constant was derived from, or `decl` itself. -/
partial def ownerOf (decl : Name) : CoreM (Option Name) := do
  let env ← getEnv
  if let some (.ctorInfo ctor) := env.find? decl then return ← ownerOf ctor.induct
  if let .str parent _ := decl then
    if (env.getProjectionFnInfo? decl).isSome then return ← ownerOf parent
    if let some (.ctorInfo ctor) := env.find? parent then return ← ownerOf ctor.induct
  if (← findDeclarationRanges? decl).isSome then return some decl
  match decl with
  | .str parent _ | .num parent _ => if parent.isAnonymous then return none else ownerOf parent
  | .anonymous => return none

def placeOf (decl : Name) : CoreM Place := do
  let env ← getEnv
  let some owner ← ownerOf decl | return .nowhere
  let some file := fileOf env owner | return .nowhere
  if handwritten file || generated file then
    match ← findDeclarationRanges? owner with
    | some ranges => return .line file ranges.range.pos.line
    | none => return .nowhere
  else if (`DY).isPrefixOf file then return .library "DyLean"
  else if (`Aeneas).isPrefixOf file then return .library "Aeneas library"
  else if (`CoreModels).isPrefixOf file || (`Hax).isPrefixOf file then
    return .library "hax core models"
  else return .nowhere

/-- A constant that Lean derived, such as a matcher or a proof term. Lean shares matchers between
declarations, so a helper says nothing about the declaration it is named after: what it mentions
counts for the declaration that uses it. -/
def helper (decl : Name) : CoreM Bool :=
  return decl.isInternalDetail && (← ownerOf decl) != some decl

def typeUses (info : ConstantInfo) : Array Name := info.type.getUsedConstants

def bodyUses (info : ConstantInfo) : Array Name :=
  match info with
  | .defnInfo d => d.value.getUsedConstants
  | .thmInfo d => d.value.getUsedConstants
  | .opaqueInfo d => d.value.getUsedConstants
  | .inductInfo d => d.ctors.toArray
  | _ => #[]

def kindOf (env : Environment) (decl : Name) : String :=
  match env.find? decl with
  | some (.thmInfo _) => "theorem"
  | some (.defnInfo _) =>
    if Meta.isInstanceCore env decl then "instance"
    else if getReducibilityStatusCore env decl == .reducible then "abbrev" else "def"
  | some (.inductInfo _) =>
    if isClass env decl then "class" else if isStructure env decl then "structure" else "inductive"
  | some (.axiomInfo _) => "axiom"
  | _ => "other"

structure Node where
  names : Array Name := #[]
  meaningUses : Std.HashSet String := {}
  proofUses : Std.HashSet String := {}

run_cmd do
  let env ← getEnv
  -- The constants of the handwritten files of this target, and the generated ones they reach.
  let mut todo : Array Name := #[]
  for (decl, _) in env.constants.toList do
    if let some file := fileOf env decl then
      if handwritten file then todo := todo.push decl
  let mut seen : NameSet := {}
  let mut nodes : Std.HashMap String Node := {}
  let mut places : Std.HashMap String Place := {}
  while !todo.isEmpty do
    let decl := todo.back!
    todo := todo.pop
    if seen.contains decl then continue
    seen := seen.insert decl
    let some info := env.find? decl | continue
    let place ← liftCoreM (placeOf decl)
    let .line file _ := place | continue
    let key := place.key
    places := places.insert key place
    let mut node := nodes.getD key {}
    if (← liftCoreM (ownerOf decl)) == some decl then
      node := { node with names := node.names.push decl }
    -- Only the proof of a theorem is a proof dependency.
    let inStatement := typeUses info ++ (if info matches .thmInfo _ then #[] else bodyUses info)
    let inProof := if info matches .thmInfo _ then bodyUses info else #[]
    for (uses, isMeaning) in [(inStatement, true), (inProof, false)] do
      let mut stack := uses
      let mut expanded : NameSet := {}
      while !stack.isEmpty do
        let used := stack.back!
        stack := stack.pop
        if expanded.contains used then continue
        expanded := expanded.insert used
        if ← liftCoreM (helper used) then
          if let some usedInfo := env.find? used then
            stack := stack ++ typeUses usedInfo ++ bodyUses usedInfo
          continue
        let target ← liftCoreM (placeOf used)
        if target == .nowhere || target.key == key then continue
        places := places.insert target.key target
        if isMeaning then node := { node with meaningUses := node.meaningUses.insert target.key }
        else node := { node with proofUses := node.proofUses.insert target.key }
        if let some usedFile := fileOf env used then
          if generated usedFile || handwritten usedFile then todo := todo.push used
    nodes := nodes.insert key node
    let _ := file
  -- Print the nodes in source order.
  let mut out : Array Json := #[]
  for (key, node) in nodes.toArray.qsort (fun a b => a.1 < b.1) do
    let some (.line file row) := places[key]? | continue
    let names := node.names.qsort (fun a b => a.toString.length < b.toString.length ||
      (a.toString.length == b.toString.length && a.toString < b.toString))
    let kinds := names.map (kindOf env)
    let meaningUses := node.meaningUses.toArray.qsort (· < ·)
    let proofUses := (node.proofUses.toArray.filter (!node.meaningUses.contains ·)).qsort (· < ·)
    out := out.push <| Json.mkObj [
      ("id", key), ("file", file.toString), ("line", row),
      ("names", toJson (names.map toString)), ("kinds", toJson kinds),
      ("cited", toJson (names.any cited.contains)),
      ("meaning", toJson meaningUses), ("proof", toJson proofUses)]
  for statement in cited do
    unless env.contains statement do throwError "no such statement: {statement}"
  IO.println (Json.arr out).pretty
