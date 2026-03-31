import HeytingLean.Blockchain.MerkleModel
import HeytingLean.Blockchain.Consensus.Spec

/-
# Consensus.MerkleProof

Semantic target for `Consensus.Spec.PropertyId.merkleProofVerification`,
grounded in the structural Merkle model and the `verifyMembership`
helper from `HeytingLean.Payments.Merkle`.

The only external assumption is an explicit bridge between propositional
equality on strings and the boolean equality used by `==`. This is
captured as a parameter `hEqImpBeq`; once a canonical `BEq`/`DecidableEq`
story for `String` is fixed, `hEqImpBeq` should be discharged from that
global instance.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace MerkleProof

open HeytingLean.Blockchain.MerkleModel
open HeytingLean.Payments.Merkle

/-- Semantic statement for `PropertyId.merkleProofVerification`. Intuitively:

    *for any tree `t`, payload `x`, and path `path` produced by `buildPath?`,
    the pure `verifyMembership` helper accepts the corresponding proof and
    reproduces the structural root.*
-/
def Statement : Prop :=
  ∀ (t : Tree) (x : String) (path : List PathElem),
    buildPath? x t = some path →
      verifyMembership { root := root t, recipient := x, path := path } =
        (true, root t)

/-- `Statement` holds as a consequence of the fully proved bridge between
    structural membership and `verifyMembership` in `MerkleModel`. -/
theorem statement_holds : Statement := by
  intro t x path h
  exact
    HeytingLean.Blockchain.MerkleModel.verifyMembership_of_buildPath?
      x t path h

end MerkleProof
end Consensus
end Blockchain
end HeytingLean
