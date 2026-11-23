module
public import Qmdb.CurrentRoot

/-! The hash-input program for a single location in Tempo's pinned MMB. Sibling references are
numbered in the compressed Rust proof order. Substituting actual proof fields into this program
reconstructs the root; looking up its item and bitmap leaves gives their public projections. -/

namespace Qmdb.Mmb
open Active
@[expose] public section

/-- The height-8 chunk subtree appears after its 256 leaves and 127 more insertions. -/
def graftedChunks (leaves : Nat) : Nat :=
  if leaves < 383 then 0 else (leaves - 383) / 256 + 1

/-- Height at bit index i of the leaf-count successor. -/
def peakHeight (u i : Nat) : Nat := i + (u / 2 ^ i) % 2

/-- Peak iterator counting down the live bits. -/
def peakHeights (u : Nat) : Nat → List Nat
  | 0 => []
  | i + 1 => peakHeight u i :: peakHeights u i

/-- Peak heights, oldest to newest, as enumerated by the pinned PeakIterator. -/
def heights (n : Nat) : List Nat := peakHeights (n + 1) (n + 1).log2

/-- Find the containing peak, returning its index, height and local leaf offset. -/
def containing : List Nat → Nat → Nat → Option (Nat × Nat × Nat)
  | [], _, _ => none
  | h :: rest, i, loc =>
    if loc < 2 ^ h then some (i, h, loc) else containing rest (i + 1) (loc - 2 ^ h)

/-- Position of the MMB subtree covering 2^height leaves beginning at start. -/
def subtreePosition (start height : Nat) : Nat :=
  let last := start + 2 ^ height - 1
  let birth := if height = 0 then last else last + 2 ^ (height - 1) - 1
  2 * birth - (birth + 1).log2 + (if height = 0 then 0 else 1)

/-- Leaf inputs of the replayed hash calls. -/
inductive Field where
  /-- Encoded operation being opened. -/
  | item
  /-- Supplied 32-byte bitmap chunk. -/
  | bitmap
  /-- An eight-byte big-endian node position, size or count. -/
  | word (n : Nat)
  /-- An entry of the compressed proof's digest list. -/
  | sibling (i : Nat)
  /-- Root of the operations tree. -/
  | ops
  /-- Digest of a complete chunk awaiting grafting. -/
  | pending
  /-- Digest of the trailing incomplete chunk. -/
  | trailing
  deriving DecidableEq

/-- Operations the pinned verifier performs over its input fields. -/
inductive Shape where
  /-- An input read by the verifier. -/
  | atom (field : Field)
  /-- A local call to the symbolic SHA-256 constructor. -/
  | hash (input : Shape)
  /-- Two consecutive inputs of a local hash call. -/
  | pair (left right : Shape)

/-- Location of a field in the hash-input program. -/
def Shape.path (f : Field) : Shape → Option (List Step)
  | .atom a => if a = f then some [] else none
  | .hash e => (e.path f).map (.hash :: ·)
  | .pair l r => ((l.path f).map (.left :: ·)).or ((r.path f).map (.right :: ·))

/-- DFS reconstruction with the cursor identifying the first of exactly h sibling digests. -/
def peakShape (graft : Bool) : Nat → Nat → Nat → Nat → Shape
  | 0, start, _, _ => .hash (.pair (.atom (.word (subtreePosition start 0))) (.atom .item))
  | h + 1, start, offset, cursor =>
    let half := 2 ^ h
    let children := if offset < half then
        .pair (peakShape graft h start offset cursor) (.atom (.sibling (cursor + h)))
      else .pair (.atom (.sibling cursor)) (peakShape graft h (start + half) (offset - half)
        (cursor + 1))
    let node := Shape.hash (.pair (.atom (.word (subtreePosition start (h + 1)))) children)
    if graft && h + 1 = 8 then .hash (.pair (.atom .bitmap) node) else node

/-- One step in peak bagging. -/
def bag (x y : Shape) : Shape := .hash (.pair x y)

/-- Bag a prefix of k additional operands forward before the final backward fold. -/
def foldFrom (k : Nat) (first : Shape) (rest : List Shape) : Shape :=
  let acc := (rest.take k).foldl bag first
  match (rest.drop k).reverse with
  | [] => acc
  | last :: rev => (acc :: rev.reverse).foldr bag last

/-- Compress the leading inactive peaks with a forward fold, then fold backward. -/
def bagPeaks (i inactive : Nat) (first : Shape) (rest : List Shape) : Shape :=
  let kept := if min i inactive = 0 then inactive else inactive - min i inactive + 1
  foldFrom (kept - 1) first rest

/-- The proof material required by an MMB location and its pinned hash-input program. -/
structure Plan where
  /-- Required number of entries in the raw digest list. -/
  count : Nat
  /-- The complete canonical current root preimage tree. -/
  tree : Shape

/-- The pinned Merkle root over nonempty peaks. -/
def merkleShape (leaves inactive : Nat) (folded : Shape) : Shape :=
  let fields := if inactive = 0 then folded else .pair (.atom (.word inactive)) folded
  .hash (.pair (.atom (.word leaves)) fields)

/-- The Merkle root over the bag and the canonical root's two optional suffix fields. -/
def envelope (leaves inactive loc : Nat) (folded : Shape) : Shape :=
  let merkle := merkleShape leaves inactive folded
  let complete := leaves / 256
  let resolved := graftedChunks leaves
  let chunkHash := Shape.hash (.atom .bitmap)
  let pend := if loc / 256 = resolved then chunkHash else .atom .pending
  let last := if loc / 256 = complete then chunkHash else .atom .trailing
  let tail := Shape.pair (.atom (.word (leaves % 256))) last
  let rhs := match decide (resolved < complete), decide (leaves % 256 ≠ 0) with
    | false, false => merkle
    | true, false => .pair merkle pend
    | false, true => .pair merkle tail
    | true, true => .pair merkle (.pair pend tail)
  .hash (.pair (.atom .ops) rhs)

/-- Insert the reconstructed peak between the compressed prefix and suffix groups. -/
def foldTarget (i inactive : Nat) (left : List Shape) (target : Shape) (right : List Shape) :
    Shape :=
  match left with
  | [] => bagPeaks i inactive target right
  | first :: rest => bagPeaks i inactive first (rest ++ target :: right)

/-- Assemble the program from the unique containing peak and the two compressed peak groups. -/
def assemble (leaves inactive loc i h offset peaks : Nat) (graft : Bool) : Plan :=
  let before := (if min i inactive = 0 then 0 else 1) + (i - inactive)
  let after := (inactive - (i + 1)) + (if max (i + 1) inactive < peaks then 1 else 0)
  let count := before + after
  let target := peakShape graft h (loc - offset) offset count
  let left := (List.range before).map fun j => Shape.atom (.sibling j)
  let right := (List.range after).map fun j => Shape.atom (.sibling (before + j))
  let folded := foldTarget i inactive left target right
  ⟨count + h, envelope leaves inactive loc folded⟩

/-- Select the location and peak layout using only the tree dimensions and the graft flag. -/
def plan (leaves inactive loc : Nat) (nonzero : Bool) : Option Plan := do
  guard (loc < leaves && leaves ≤ 0x400000000000001e)
  let peaks := heights leaves
  guard (inactive ≤ peaks.length)
  let (i, h, off) ← containing peaks 0 loc
  return assemble leaves inactive loc i h off peaks.length
    (nonzero && loc / 256 < graftedChunks leaves)

/-- Project the item and its chunk within the very same replay program. -/
def currentPaths (leaves inactive loc : Nat) (nonzero : Bool) :
    Option (List Step × Option (List Step)) := do
  let recipe ← plan leaves inactive loc nonzero
  let item ← recipe.tree.path .item
  return (item, recipe.tree.path .bitmap)

end
end Qmdb.Mmb
