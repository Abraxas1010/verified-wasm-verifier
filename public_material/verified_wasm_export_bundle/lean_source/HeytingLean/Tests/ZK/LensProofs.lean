import HeytingLean.Crypto.ZK.LensProofs
import HeytingLean.Bridges.Tensor
import HeytingLean.Bridges.Graph
import HeytingLean.Bridges.Clifford

/-!
# Tests — ZK LensProofs scaffolding

Type-check the LensProofs API and basic equivalences.
-/

namespace HeytingLean
namespace Tests
namespace ZK

open HeytingLean.LoF
open HeytingLean.Crypto
open HeytingLean.Crypto.ZK
open HeytingLean.Crypto.ZK.LensProofs

universe u

section
variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α)

-- Bridge model variables
variable (MT : HeytingLean.Bridges.Tensor.Model α)
variable (MG : HeytingLean.Bridges.Graph.Model α)
variable (MC : HeytingLean.Bridges.Clifford.Model α)

-- Basic API checks
#check ProofCore (R := R)
#check ProofWith (R := R)

-- Verify top on each lens
#check verifyTensor_top (R := R) MT
#check verifyGraph_top (R := R) MG
#check verifyClifford_top (R := R) MC

-- Cross-lens equivalence
variable {n : ℕ} (φ : Form n)
#check tensor_iff_graph (R := R) MT MG φ
#check tensor_iff_clifford (R := R) MT MC φ
#check graph_iff_clifford (R := R) MG MC φ

-- Simple 2-var conjunction is verifiable on each lens
#check LensProofs.Examples.φAnd2
#check LensProofs.Examples.verifyTensor_and2 (R := R) MT
#check LensProofs.Examples.verifyGraph_and2 (R := R) MG
#check LensProofs.Examples.verifyClifford_and2 (R := R) MC

-- Bottom is not verifiable on any lens
#check LensProofs.Examples.not_verifyTensor_bot (R := R) MT
#check LensProofs.Examples.not_verifyGraph_bot (R := R) MG
#check LensProofs.Examples.not_verifyClifford_bot (R := R) MC

end

end ZK
end Tests
end HeytingLean
