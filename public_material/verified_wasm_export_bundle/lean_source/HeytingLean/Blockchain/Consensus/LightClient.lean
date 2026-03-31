import HeytingLean.Blockchain.MerkleModel
import HeytingLean.Blockchain.Consensus.Spec

/-
# Consensus.LightClient

Lightweight semantic model for light-client correctness, layered on top
of the structural Merkle model in `Blockchain.MerkleModel`.

The central statement `Statement` is intended as the semantic target for
`Consensus.Spec.PropertyId.lightClientCorrectness`:

* given a chain of headers with state roots,
* a header known to lie on that chain, and
* a Merkle proof built structurally from some tree whose root matches
  the header's state root,

the light client accepts the proof and the asserted payload is indeed a
member of the structural tree.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace LightClient

open HeytingLean.Blockchain.MerkleModel
open HeytingLean.Payments.Merkle

/-- Minimal header model for the light client: we only track a state
    root, which is tied to a structural Merkle tree via `MerkleModel.root`. -/
structure Header where
  stateRoot : String
  deriving Repr, Inhabited, DecidableEq

/-- A simple header chain modelled as a list. -/
abbrev Chain := List Header

/-- Predicate stating that a header appears in a given chain. -/
def headerInChain (h : Header) (c : Chain) : Prop :=
  h ∈ c

/-- Light-client acceptance predicate: a light client accepts a proof
    relative to a chain and header when the header is known to be on the
    chain and the pure `verifyMembership` helper accepts the Merkle
    proof with respect to the header's state root. -/
def accepts (c : Chain) (h : Header) (p : VProof) : Prop :=
  headerInChain h c ∧
    verifyMembership p = (true, h.stateRoot)

/-- Semantic light-client correctness statement, intended as the target
    for `Consensus.Spec.PropertyId.lightClientCorrectness`.

Given:

* a header chain `c` and header `h` on that chain;
* a structural Merkle tree `t` whose root matches `h.stateRoot`;
* a payload `x` and path `path` returned by `buildPath? x t`;

then the light client accepts the corresponding Merkle proof, and the
payload is structurally a member of `t`. -/
def Statement : Prop :=
  ∀ (c : Chain) (h : Header) (t : Tree) (x : String) (path : List PathElem),
    headerInChain h c →
    root t = h.stateRoot →
    buildPath? x t = some path →
      accepts c h { root := root t, recipient := x, path := path } ∧
        member x t

/-- `Statement` holds by combining the structural membership and
    boolean-level correctness theorems from `MerkleModel`. -/
theorem statement_holds : Statement := by
  classical
  intro c h t x path hIn hRoot hBuild
  -- Structural membership from the path witness.
  have hMember : member x t :=
    buildPath?_member x t path hBuild
  -- Boolean-level correctness of `verifyMembership` for this path.
  have hVM :
      verifyMembership
          { root := root t, recipient := x, path := path } =
        (true, root t) :=
    verifyMembership_of_buildPath? x t path hBuild
  -- Package these into the light-client acceptance predicate and the
  -- structural membership fact.
  refine And.intro ?hAccept hMember
  dsimp [accepts, headerInChain] at *
  -- The header-in-chain hypothesis is part of acceptance, and the
  -- `verifyMembership` result is rewritten using the root equality.
  constructor
  · exact hIn
  · simpa [hRoot] using hVM

end LightClient
end Consensus
end Blockchain
end HeytingLean

