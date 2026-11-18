module
public import DY.EquationalTheory.Hash
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.Literal

namespace Qmdb
open DY
@[expose] public section

-- The minimal constructor instance used here follows Examples/MerkleTree/Instance.
#combine +toplevel into BytesFunctor, BytesLength from
  Literal,
  Concat,
  Hash,

def be64 (n : Nat) : ByteArray :=
  ⟨((List.range 8).map fun i => UInt8.ofNat (n / 256^(7-i))).toArray⟩

def leaf (p : Nat) (item : ByteArray) : Bytes :=
  Hash.hash (Concat.concat (Literal.literalToBytes (be64 p)) (Literal.literalToBytes item))

def node (p : Nat) (left right : Bytes) : Bytes :=
  Hash.hash (Concat.concat (Literal.literalToBytes (be64 p)) (Concat.concat left right))

def wrap (height : Nat) (peak : Bytes) : Bytes :=
  Hash.hash (Concat.concat (Literal.literalToBytes (ByteArray.mk #[0,0] ++ be64 (2^height))) peak)

-- An independent honest tree, indexed by absolute leaf location.
def tree (items : Nat → ByteArray) : Nat → Nat → Nat → Bytes
  | 0, p, start => leaf p (items start)
  | h+1, p, start => node p (tree items h (p-2^(h+1)) start)
      (tree items h (p-1) (start+2^h))

-- Consume the outside subtree digest in the order of a left-first DFS.
def replay (item : ByteArray) : Nat → Nat → Nat → Nat → List Bytes → Option (Bytes × List Bytes)
  | 0, p, _, _, ws => some (leaf p item, ws)
  | h+1, p, start, loc, ws => do
    if loc < start+2^h then
      let (left, right::rest) ← replay item h (p-2^(h+1)) start loc ws | none
      return (node p left right, rest)
    else
      let left::tail := ws | none
      let (right, rest) ← replay item h (p-1) (start+2^h) loc tail
      return (node p left right, rest)

def accepts (h loc : Nat) (root : Bytes) (item : ByteArray) (ws : List Bytes) : Prop :=
  h ≤ 63 ∧ loc < 2^h ∧ ∃ peak, replay item h (2*(2^h-1)) 0 loc ws = some (peak, []) ∧
    wrap h peak = root

end
end Qmdb
