import HeytingLean.LambdaIR.Integrator
import HeytingLean.Quantum.TWA.ToSDE

namespace HeytingLean
namespace Tests
namespace Quantum
namespace TWA

open HeytingLean.Quantum.TWA
open HeytingLean.LambdaIR.SDE

/-! Regression checks for Phase 2 (TWA → SDE + integrator). -/

example : Fintype.card (StateIndex 1) = 3 := by
  calc
    Fintype.card (StateIndex 1) = 3 * 1 := card_stateIndex (N := 1)
    _ = 3 := by simp

example (dt : ℝ) (x : (Fin 2 → ℝ)) :
    eulerStep (S := SDESystem.zero (ι := Fin 2) (κ := Fin 0)) dt (fun j => nomatch j) x = x := by
  simp

example (dt : ℝ) (x : (Fin 2 → ℝ)) :
    stratonovichStep (S := SDESystem.zero (ι := Fin 2) (κ := Fin 0)) dt (fun j => nomatch j) x = x := by
  simp

/-! A tiny TWA→SDE instantiation: 1 spin, no jumps, constant field. -/

def S1 : LindbladSpec :=
  { N := 1
    nJumps := 0
    H := fun _ => 0
    jumps := fun j => nomatch j
    Γ := 0
    Γ_psd := by
      simpa using (HeytingLean.Quantum.PosSemidef.zero (ι := Fin 0)) }

def D1 : Dynamics S1 :=
  { field := fun _ => fun _ => ⟨0, 0, 0⟩
    diffusion := fun _ => 0 }

example (x : StateVec S1.N) (i : Fin S1.N) :
    let s : SpinConfig S1.N := spinConfigOfStateVec (N := S1.N) x
    SpinVector.dot (s i) (SpinVector.hamiltonianVF (D1.field s i) (s i)) = 0 := by
  simpa using (Dynamics.drift_tangent_eachSpin (S := S1) (D := D1) (x := x) (i := i))

end TWA
end Quantum
end Tests
end HeytingLean
