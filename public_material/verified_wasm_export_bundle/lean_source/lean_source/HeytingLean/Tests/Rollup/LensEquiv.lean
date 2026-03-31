import HeytingLean.Blockchain.Rollup.StateTransition
import HeytingLean.Blockchain.Rollup.MultiLens
import HeytingLean.Bridges.Tensor
import HeytingLean.Bridges.Graph
import HeytingLean.Bridges.Clifford

/-!
# Tests — Rollup Multi-Lens Scaffolding

Type-check basic components to ensure the scaffolding integrates. Concrete
examples and equivalence proofs will be added in subsequent phases.
-/

namespace HeytingLean
namespace Tests
namespace Rollup

open HeytingLean.LoF
open HeytingLean.Blockchain
open HeytingLean.Blockchain.Rollup

universe u v

section
variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α)
variable {n : ℕ}

-- Abstract spec variables
variable (S : Rollup.Spec (R := R) n)

-- #check the core pieces
#check Rollup.Spec.validTransition (R := R) (S := S)
#check Rollup.Spec.program (R := R) (S := S)

-- #check lens-agnostic verifier
section LensVerifier
open HeytingLean.Crypto
variable (L : Lens (R := R))
#check Rollup.Spec.verifyWith (R := R) (S := S) L
end LensVerifier

-- Cross-lens equivalence theorems (now require hR constraints)
#check @Rollup.Verify.tensor_iff_graph α _ R n S
#check @Rollup.Verify.tensor_iff_clifford α _ R n S
#check @Rollup.Verify.graph_iff_clifford α _ R n S

-- Trivial spec: a transition that always evaluates to ⊤.
def TrivialSpec (R : Reentry α) : Rollup.Spec (R := R) 1 :=
  { State := Nat
    transitionForm := fun _ _ => HeytingLean.Crypto.Form.top
    env := fun _ _ => fun _ => (⊤ : R.Omega) }

-- Use the built-in trivial example from the Rollup module
#check HeytingLean.Blockchain.Rollup.Examples.demoSpec (R := R)
#check (Rollup.Spec.validTransition (R := R) (S := HeytingLean.Blockchain.Rollup.Examples.demoSpec (R := R)) : _ → _ → Prop)

-- Counter example: check Counter type and acceptance lemma
#check HeytingLean.Blockchain.Rollup.Counter
#check HeytingLean.Blockchain.Rollup.counter (R := R)
#check HeytingLean.Blockchain.Rollup.counter_accept (R := R)

-- Example with concrete model that has matching R
-- (When M.R = R is definitionally equal, the hR parameter is inferred by rfl)
section ConcreteModels
variable (MT : HeytingLean.Bridges.Tensor.Model α) (hMT : MT.R = R)
variable (MG : HeytingLean.Bridges.Graph.Model α) (hMG : MG.R = R)
variable (MC : HeytingLean.Bridges.Clifford.Model α) (hMC : MC.R = R)

-- Per-lens specialisations with explicit hR
#check Rollup.Verify.tensor (R := R) (S := S) MT hMT
#check Rollup.Verify.graph (R := R) (S := S) MG hMG
#check Rollup.Verify.clifford (R := R) (S := S) MC hMC

-- Acceptance lemmas with explicit hR
#check @HeytingLean.Blockchain.Rollup.Examples.demoSpec_tensor α _ R MT hMT
#check @HeytingLean.Blockchain.Rollup.Examples.demoSpec_graph α _ R MG hMG
#check @HeytingLean.Blockchain.Rollup.Examples.demoSpec_clifford α _ R MC hMC

#check @HeytingLean.Blockchain.Rollup.Examples.counter_tensor_accept α _ R MT hMT
#check @HeytingLean.Blockchain.Rollup.Examples.counter_graph_accept α _ R MG hMG
#check @HeytingLean.Blockchain.Rollup.Examples.counter_clifford_accept α _ R MC hMC

end ConcreteModels

end

end Rollup
end Tests
end HeytingLean
