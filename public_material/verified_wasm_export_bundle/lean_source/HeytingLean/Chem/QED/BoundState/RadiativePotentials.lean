import Mathlib.Data.String.Basic
import HeytingLean.Chem.Foundations.Terms

/-!
# Radiative (QED) correction terms for bound states (interface-only)

We treat radiative corrections as *named* potential/energy-correction terms that can later be given
semantics (analytic formulae, EFT operator expansions, or external numeric evaluation).

At M0 we only define the taxonomy and provenance hooks.
-/

namespace HeytingLean
namespace Chem
namespace QED
namespace BoundState

open HeytingLean.Chem.Foundations

/-- A small tag set for QED correction families relevant to atoms/molecules. -/
inductive RadiativeCorrection where
  /-- Vacuum polarization, often represented via the Uehling potential. -/
  | vacuumPolarization
  /-- Electron self-energy contribution (Lamb shift family). -/
  | selfEnergy
  /-- Mixed (two-loop and/or higher-order) corrections not yet refined. -/
  | higherOrder
deriving DecidableEq, Repr

/-- A correction term with a human-readable name and provenance metadata. -/
structure CorrectionTerm where
  tag        : RadiativeCorrection
  name       : String
  provenance : Provenance

/-- Vacuum polarization (Uehling potential) correction term (provenance-first). -/
def uehling : CorrectionTerm :=
  { tag := .vacuumPolarization
    name := "Uehling vacuum polarization potential"
    provenance :=
      { source := "Uehling (Phys. Rev. 48 (1935) 55)"
        url := "https://www.osti.gov/biblio/7382162"
        note := "Canonical reference for the vacuum polarization potential term used in bound-state QED models." } }

/-- Lamb shift discovery provenance hook. This is a marker term; semantics added in later phases. -/
def lambShift : CorrectionTerm :=
  { tag := .selfEnergy
    name := "Lamb shift (self-energy family)"
    provenance :=
      { source := "Lamb and Retherford (Phys. Rev. 72 (1947) 241)"
        url := "https://journals.aps.org/pr/abstract/10.1103/PhysRev.72.241"
        note := "Empirical discovery motivating self-energy/radiative corrections in bound-state models." } }

end BoundState
end QED
end Chem
end HeytingLean

