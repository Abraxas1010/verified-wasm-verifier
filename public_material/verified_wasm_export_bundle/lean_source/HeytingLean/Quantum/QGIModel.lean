import Mathlib.Data.Complex.Basic
import HeytingLean.Quantum.Phase
import HeytingLean.Quantum.GravitationalCollapse
import HeytingLean.Quantum.QGIPhaseLaw
import HeytingLean.Quantum.OML.Examples.QGIInterferometer

/-!
# QGI example model: amplitudes and phase profiles

This module ties together:

* the QGI-style orthomodular lattice `QGIβ` from
  `Quantum.OML.Examples.QGIInterferometer`,
* the minimal phase form `minimalPhaseForm` from `Quantum.Phase`, and
* the symbolic T³ phase law from `QGIPhaseLaw`.

The goal is not to build a full Hilbert-space model but to provide a
lightweight, symbolic “wavefunction-like” assignment and an
`interferencePhase` quantity that can be related to `t3Phase` under
explicit assumptions.
-/

namespace HeytingLean
namespace Quantum
namespace QGIModel

open Quantum
open Quantum.Phase
open Quantum.GravitationalCollapse
open Quantum.QGIPhaseLaw
open Quantum.OML
open Quantum.OML.QGIInterferometer
open H2

/-- A symbolic phase profile for the two arms of the QGI example. -/
structure PhaseProfile where
  /-- Phase associated with the laboratory arm as a function of time. -/
  φ_lab  : ℝ → ℝ
  /-- Phase associated with the free-fall arm as a function of time. -/
  φ_free : ℝ → ℝ

/-- A simple “wavefunction-like” amplitude assignment on `QGIβ` for a
    given phase profile at time `T`.

For the purposes of this minimal example we only ascribe non-zero amplitudes
to the two distinguished path propositions; the bottom and top elements
are given amplitude `0`. -/
noncomputable def amp (Φ : PhaseProfile) (T : ℝ) : QGIβ → ℂ
  | bot => 0
  | top => 0
  | X   => minimalPhaseForm (Φ.φ_lab T)
  | Y   => minimalPhaseForm (Φ.φ_free T)

/-- Amplitude on the laboratory arm. -/
lemma amp_lab (Φ : PhaseProfile) (T : ℝ) :
    amp Φ T labPath = minimalPhaseForm (Φ.φ_lab T) := by
  rfl

/-- Amplitude on the free-fall arm. -/
lemma amp_free (Φ : PhaseProfile) (T : ℝ) :
    amp Φ T freePath = minimalPhaseForm (Φ.φ_free T) := by
  rfl

/-- A symbolic interference phase between the two QGI arms, modelled as
    the difference between their underlying real phase profiles. -/
noncomputable def interferencePhase (Φ : PhaseProfile) (T : ℝ) : ℝ :=
  Φ.φ_free T - Φ.φ_lab T

/-- If a phase profile is chosen so that the difference between the
    free-fall and laboratory phases follows the T³ profile, then the
    interference phase agrees with the real-valued `t3PhaseR` at that
    time. -/
lemma interferencePhase_eq_t3
    (P : PhysParams) (m g T : ℝ) (Φ : PhaseProfile)
    (hΦ : Φ.φ_free T - Φ.φ_lab T = t3PhaseR P m g T) :
    interferencePhase Φ T = t3PhaseR P m g T := by
  simp [interferencePhase, hΦ]

end QGIModel
end Quantum
end HeytingLean
