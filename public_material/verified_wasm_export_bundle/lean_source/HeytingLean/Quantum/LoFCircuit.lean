import HeytingLean.Quantum.LoFBloch

/-!
# LoF Circuits (laptop-scale)

Small circuit wrapper over the Bloch-style `LoFState` model.
-/

namespace HeytingLean
namespace Quantum

/-- A minimal gate set (extend as needed). -/
inductive LoFGate where
  | X | Y | Z | H
deriving Repr, DecidableEq

abbrev Circuit := List LoFGate

def applyGate : LoFGate → LoFState → LoFState
  | .X => gateX
  | .Y => gateY
  | .Z => gateZ
  | .H => gateH

def runCircuit (c : Circuit) (s0 : LoFState) : LoFState :=
  c.foldl (fun s g => applyGate g s) s0

/-! ## Tiny regression examples -/

def createPlus : Circuit := [.H]

theorem createPlus_correct : runCircuit createPlus LoFState.void = LoFState.reentry := by
  simp [createPlus, runCircuit, applyGate, LoFState.void, LoFState.reentry, gateH]

end Quantum
end HeytingLean

