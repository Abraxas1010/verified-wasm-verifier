import HeytingLean.Logic.Dialectic
import HeytingLean.LoF.Nucleus
import HeytingLean.Logic.ModalDial

namespace HeytingLean
namespace Tests

open HeytingLean.Logic
open HeytingLean.Logic.Dialectic
open HeytingLean.LoF

section
variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α)
variable (T A : α)

-- Basic synthesis objects/lemmas check at the right types.
#check synth R T A
#check synth_idempotent (R := R) (T := T) (A := A)
#check synthesis_fixed (R := R) (T := T) (A := A)
#check le_synth_left (R := R) (T := T) (A := A)
#check le_synth_right (R := R) (T := T) (A := A)

variable {W : α}

-- Minimality principle: if W is R-fixed and above both T and A, synthesis ≤ W.
#check (fun (hT : T ≤ W) (hA : A ≤ W) (hW : R W = W) =>
  synthesis_least (R := R) (T := T) (A := A) (W := W) hT hA hW)

-- Fixed-point lattice variant.
variable (TO AO : R.Omega)
#check synthOmega (R := R) TO AO
#check (synthOmega_le (R := R))
#check (synthOmega_self (R := R))

-- Primordial oscillation element and Euler boundary relation.
#check Dialectic.oscillationOmega (R := R)
#check Dialectic.eulerBoundary_le_oscillation (R := R)

-- Dial integration: collapse/expand invariance for synthesis.
variable (n : ℕ)
#check HeytingLean.Logic.Modal.DialParam.collapseAt_synth (R := R) (n := n) (T := T) (A := A)
#check HeytingLean.Logic.Modal.DialParam.expandAt_synth (R := R) (n := n) (T := T) (A := A)

end

end Tests
end HeytingLean
