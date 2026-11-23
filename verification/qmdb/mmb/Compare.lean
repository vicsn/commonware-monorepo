import Qmdb.Mmb.Raw

open Qmdb DY

private def render (path : List Active.Step) : String :=
  String.ofList (path.map fun | .hash => 'H' | .left => 'L' | .right => 'R')

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def unhex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    return UInt8.ofNat ((← hexDigit a) * 16 + (← hexDigit b)) :: (← unhex rest)
  | [_] => none

private def digest (s : String) : IO Bytes := do
  let some bytes := unhex s.toList | throw (IO.userError "malformed hex")
  unless bytes.length = 32 do throw (IO.userError "wrong digest length")
  return Literal.literalToBytes ⟨bytes.toArray⟩

private def hex (b : ByteArray) : String := Id.run do
  let alphabet := "0123456789abcdef".toList.toArray
  let mut out := ""
  for i in b.data do
    out := out.push alphabet[i.toNat / 16]! |>.push alphabet[i.toNat % 16]!
  return out

private def trace : Mmb.Expr → String
  | .hash e => "H" ++ trace e
  | .pair a b => "(" ++ trace a ++ "," ++ trace b ++ ")"
  | .atom x => (Literal.bytesToLiteral x).map hex |>.getD "opaque nonliteral"

def main (args : List String) : IO Unit := do
  let [file] := args | throw (IO.userError "expected the Rust trace file")
  let rows ← IO.FS.lines file
  if rows.isEmpty then throw (IO.userError "empty Rust trace")
  for line in rows do
    let [n, i, l, op, bitmap, ops, arbitrary, siblings, actual] := line.splitOn " "
      | throw (IO.userError s!"malformed Rust trace: {line}")
    let (leaves, inactive, loc) := (n.toNat!, i.toNat!, l.toNat!)
    let some (item, some chunk) := Mmb.currentPaths leaves inactive loc true
      | throw (IO.userError s!"Lean rejected Rust layout: {line}")
    unless render item == op && render chunk == bitmap do
      throw (IO.userError s!"Rust: {line}\nLean: {render item} {render chunk}")
    let bm : Active.Chunk := Vector.replicate 32 0xbd
    let opaqueDigest ← digest arbitrary
    let item := Active.literal (Vector.replicate 32 0x3a)
    let suffix := fun index => if loc / 256 = index then Hash.hash (Active.literal bm) else opaqueDigest
    let complete := leaves / 256
    let resolved := Mmb.graftedChunks leaves
    let digests ← if siblings.isEmpty then pure [] else (siblings.splitOn ",").mapM digest
    let proof : Mmb.RawProof :=
      ⟨digests, ← digest ops, if resolved < complete then some (suffix resolved) else none,
        if leaves % 256 ≠ 0 then some (suffix complete) else none, bm⟩
    let some expr := proof.reconstruct leaves inactive loc item
      | throw (IO.userError s!"Lean rejected accepted proof: {line}")
    unless trace expr == actual do
      throw (IO.userError s!"Rust: {actual}\nLean: {trace expr}\nleaves={n} inactive={i} loc={l}")
    unless proof.verify expr.value leaves inactive loc item do
      throw (IO.userError s!"Verifier rejected matching root: {line}")
    let rejects := fun (claim : Mmb.RawProof) => !claim.verify expr.value leaves inactive loc item
    let wrongTail := match proof.trailing with
      | none => some opaqueDigest
      | some _ => none
    let extra := { proof with digests := digests ++ [opaqueDigest] }
    let shorter := { proof with digests := digests.dropLast }
    let zeroed := { proof with chunk := Vector.replicate 32 0 }
    unless rejects extra && (digests.isEmpty || rejects shorter) && rejects zeroed &&
        rejects { proof with trailing := wrongTail } &&
        !proof.verify opaqueDigest leaves inactive loc item &&
        !proof.verify expr.value leaves inactive loc (Active.literal (Vector.replicate 32 0x3b)) do
      throw (IO.userError s!"Lean accepted a rejected Rust mutation: {line}")
  IO.println s!"Matched all paths, full hash preimages and verdicts for {rows.size} production proofs."
