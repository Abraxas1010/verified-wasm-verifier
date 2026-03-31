import HeytingLean.Quantum.QFreeEnergy
import HeytingLean.Quantum.QChannel
import HeytingLean.Quantum.ActiveInference.PartialTrace
import HeytingLean.Quantum.ActiveInference.PartialTraceDiag
import HeytingLean.Quantum.ActiveInference.OperatorPinching

/-
Reduced context file for the CPTP data-processing inequality. The statement is intentionally kept
abstract: a Kraus channel together with pre/post densities satisfying the
expected trace-preserving equations.
-/

namespace HeytingLean
namespace Quantum
namespace ActiveInference

open Quantum KrausChannel
open scoped Matrix
open Matrix Complex

noncomputable section

set_option linter.unusedVariables false

/-- Data needed to express CPTP monotonicity in a finite-dimensional setting. -/
structure CptpScenario (n m : ℕ) where
  Φ : KrausChannel n m
  ρ : Density n
  σ : Density n
  ρOut : Density m
  σOut : Density m
  mapρ : ρOut.mat = Φ.map ρ.mat
  mapσ : σOut.mat = Φ.map σ.mat

/-- Statement of the CPTP data-processing inequality; the proof is pending a
  spectral argument. -/
def qRelEntCptpStatement {n m : ℕ} (S : CptpScenario n m) : Prop :=
  qRelEnt S.ρOut S.σOut ≤ qRelEnt S.ρ S.σ

lemma qRelEntCptpStatement_partialTrace {n m : ℕ}
    (S : CptpScenario n m) :
    qRelEntCptpStatement S ↔
      qRelEnt
          (partialTraceDensity
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.ρ))
          (partialTraceDensity
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.σ))
        ≤ qRelEnt S.ρ S.σ := by
  classical
  have hρmat :
      S.ρOut.mat =
        (partialTraceDensity
          (isometryExtendDensity S.Φ.isometryMatrix
            S.Φ.isometryMatrix_isometry S.ρ)).mat :=
    (S.mapρ.trans
      (_root_.HeytingLean.Quantum.ActiveInference.KrausChannel.map_eq_partialTrace
        (Φ := S.Φ) (ρ := S.ρ))).trans rfl
  have hσmat :
      S.σOut.mat =
        (partialTraceDensity
          (isometryExtendDensity S.Φ.isometryMatrix
            S.Φ.isometryMatrix_isometry S.σ)).mat :=
    (S.mapσ.trans
      (_root_.HeytingLean.Quantum.ActiveInference.KrausChannel.map_eq_partialTrace
        (Φ := S.Φ) (ρ := S.σ))).trans rfl
  have hrewrite :
      qRelEnt S.ρOut S.σOut =
        qRelEnt
          (partialTraceDensity
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.ρ))
          (partialTraceDensity
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.σ)) :=
    qRelEnt_congr hρmat hσmat
  constructor
  · intro h
    simpa [qRelEntCptpStatement, hrewrite] using h
  · intro h
    simpa [qRelEntCptpStatement, hrewrite.symm] using h

lemma qRelEntCptpStatement_partialTrace_vs_isometryExtend {n m : ℕ}
    (S : CptpScenario n m) :
    qRelEntCptpStatement S ↔
      qRelEnt
          (partialTraceDensity
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.ρ))
          (partialTraceDensity
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.σ))
        ≤ qRelEnt
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.ρ)
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.σ) := by
  classical
  have hPT := qRelEntCptpStatement_partialTrace (S := S)
  have hIso :
      qRelEnt
          (isometryExtendDensity S.Φ.isometryMatrix
            S.Φ.isometryMatrix_isometry S.ρ)
          (isometryExtendDensity S.Φ.isometryMatrix
            S.Φ.isometryMatrix_isometry S.σ) =
        qRelEnt S.ρ S.σ := by
    simpa using
      (qRelEnt_isometryExtendDensity
        (m := m * S.Φ.numOps) (k := n)
        (V := S.Φ.isometryMatrix)
        (hV := S.Φ.isometryMatrix_isometry)
        (ρ := S.ρ) (σ := S.σ))
  constructor
  · intro h
    have hineq := (Iff.mp hPT h)
    simpa [hIso.symm] using hineq
  · intro h
    have hineq :
        qRelEnt
            (partialTraceDensity
              (isometryExtendDensity S.Φ.isometryMatrix
                S.Φ.isometryMatrix_isometry S.ρ))
            (partialTraceDensity
              (isometryExtendDensity S.Φ.isometryMatrix
                S.Φ.isometryMatrix_isometry S.σ))
          ≤ qRelEnt S.ρ S.σ := by
      simpa [hIso] using h
    exact (Iff.mpr hPT hineq)

lemma qRelEntCptpStatement_pinchedPartialTrace {n m : ℕ}
    (S : CptpScenario n m) :
    qRelEntCptpStatement S ↔
      qRelEnt
          (partialTraceDensity
            (pinchAncillaDensity (m:=m) (k:=S.Φ.numOps)
              (isometryExtendDensity S.Φ.isometryMatrix
                S.Φ.isometryMatrix_isometry S.ρ)))
          (partialTraceDensity
            (pinchAncillaDensity (m:=m) (k:=S.Φ.numOps)
              (isometryExtendDensity S.Φ.isometryMatrix
                S.Φ.isometryMatrix_isometry S.σ)))
        ≤ qRelEnt S.ρ S.σ := by
  classical
  have hPT :=
    qRelEntCptpStatement_partialTrace (S := S)
  have hρ :
      partialTraceDensity
          (pinchAncillaDensity (m:=m) (k:=S.Φ.numOps)
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.ρ)) =
        partialTraceDensity
          (isometryExtendDensity S.Φ.isometryMatrix
            S.Φ.isometryMatrix_isometry S.ρ) := by
    simpa using
      (partialTraceDensity_pinchAncilla
        (m:=m) (k:=S.Φ.numOps)
        (ρ :=
          isometryExtendDensity S.Φ.isometryMatrix
            S.Φ.isometryMatrix_isometry S.ρ))
  have hσ :
      partialTraceDensity
          (pinchAncillaDensity (m:=m) (k:=S.Φ.numOps)
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.σ)) =
        partialTraceDensity
          (isometryExtendDensity S.Φ.isometryMatrix
            S.Φ.isometryMatrix_isometry S.σ) := by
    simpa using
      (partialTraceDensity_pinchAncilla
        (m:=m) (k:=S.Φ.numOps)
        (ρ :=
          isometryExtendDensity S.Φ.isometryMatrix
            S.Φ.isometryMatrix_isometry S.σ))
  have hrewrite :
      qRelEnt
          (partialTraceDensity
            (pinchAncillaDensity (m:=m) (k:=S.Φ.numOps)
              (isometryExtendDensity S.Φ.isometryMatrix
                S.Φ.isometryMatrix_isometry S.ρ)))
          (partialTraceDensity
            (pinchAncillaDensity (m:=m) (k:=S.Φ.numOps)
              (isometryExtendDensity S.Φ.isometryMatrix
                S.Φ.isometryMatrix_isometry S.σ))) =
        qRelEnt
          (partialTraceDensity
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.ρ))
          (partialTraceDensity
            (isometryExtendDensity S.Φ.isometryMatrix
              S.Φ.isometryMatrix_isometry S.σ)) :=
    qRelEnt_congr hρ hσ
  constructor
  · intro h
    have hineq := (Iff.mp hPT h)
    simpa [hrewrite] using hineq
  · intro h
    have hineq :
        qRelEnt
            (partialTraceDensity
              (isometryExtendDensity S.Φ.isometryMatrix
                S.Φ.isometryMatrix_isometry S.ρ))
            (partialTraceDensity
              (isometryExtendDensity S.Φ.isometryMatrix
                S.Φ.isometryMatrix_isometry S.σ))
          ≤ qRelEnt S.ρ S.σ := by
      simpa [hrewrite] using h
    exact (Iff.mpr hPT hineq)

end

end ActiveInference
end Quantum
end HeytingLean
