module
public import Commonware.Symbolic.Terms

/-! The leaf target's term algebra and the input that the application supplies. Trusted.
`#combine` fixes DyLean's bytes to literals, concatenation and hashing. `Commitment` is the trusted
digest together with the item that it commits to: the digest is the production leaf digest of that
item. -/

namespace Leaf
open DY Aeneas Aeneas.Std CoreModels Commonware.Symbolic commonware_symbolic
@[expose] public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Literal,
  Concat,
  Hash,

/-- A trusted commitment: the production leaf digest of `item`. -/
class Commitment where
  digest : Bytes
  item : Slice Std.U8
  honest : terms.leaf_digest dyTerms () leaf.POSITION item = RustM.ok digest

end
end Leaf
