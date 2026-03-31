import HeytingLean.Bridges.JRatchet.JRatchetCore
import HeytingLean.Representations.Radial.JRatchet
import HeytingLean.Bridge.Assembly.RatchetCorrespondence
import HeytingLean.Genesis.EigenformSoup.Invariants

/-!
# Conversions: selected J-ratchet variants → RatchetWitness

This module provides `RatchetWitness` constructors for the variant
families whose Lean formalizations expose a `RatchetTrajectory`:

1. Radial JState (`spentFuel` monotonicity)
2. Assembly index (`assemblyRatchetTrajectory`)
3. EigenformSoup (`jRatchetTrajectory`)
4. Constant trajectory (trivial, any domain)

Variants without explicit conversion here (StrictRatchet stages,
DimensionalRatchet, Veselov genetic code, RatchetStep/Tower) either
operate at a different categorical level (nuclei, not `Nat → Nat`)
or lack an exported `RatchetTrajectory` witness in their current
formalization. The registry (`JRatchetRegistry`) tracks all 13
known variants regardless of conversion coverage.
-/

namespace HeytingLean
namespace Bridges
namespace JRatchet

open HeytingLean.Topos.JRatchet

/-! ## 1. Radial JState → RatchetWitness -/

noncomputable def radialToWitness
    {G : HeytingLean.Representations.Radial.RadialGraph}
    (js : HeytingLean.Representations.Radial.JRatchet.JState G) :
    RatchetWitness where
  level := HeytingLean.Representations.Radial.JRatchet.JState.spentFuel js
  monotone := radial_spentFuel_trajectory (js := js)

/-! ## 2. Assembly index → RatchetWitness -/

def assemblyToWitness
    {α : Type _} [DecidableEq α]
    (R : ATheory.Rules α)
    (o : ATheory.Obj α) :
    RatchetWitness where
  level := Bridge.Assembly.assemblyRatchetLevel R o
  monotone := Bridge.Assembly.assemblyRatchetTrajectory R o

/-! ## 3. EigenformSoup → RatchetWitness -/

def eigenformSoupToWitness
    {nuc : Genesis.EigenformSoup.SoupNucleus}
    (s : Genesis.EigenformSoup.SoupState nuc) :
    RatchetWitness where
  level := fun fuel => Genesis.EigenformSoup.jRatchetLevel (Genesis.EigenformSoup.runSoupAux fuel s)
  monotone := Genesis.EigenformSoup.jRatchetTrajectory (nuc := nuc) s

/-! ## 4. Constant trajectory (trivial witness for any domain) -/

def constToWitness (n : Nat) : RatchetWitness :=
  RatchetWitness.const n

/-! ## Roundtrip: witness extraction preserves the trajectory -/

theorem radialToWitness_level
    {G : HeytingLean.Representations.Radial.RadialGraph}
    (js : HeytingLean.Representations.Radial.JRatchet.JState G) :
    (radialToWitness js).level =
      HeytingLean.Representations.Radial.JRatchet.JState.spentFuel js := rfl

theorem assemblyToWitness_level
    {α : Type _} [DecidableEq α]
    (R : ATheory.Rules α)
    (o : ATheory.Obj α) :
    (assemblyToWitness R o).level = Bridge.Assembly.assemblyRatchetLevel R o := rfl

theorem eigenformSoupToWitness_level
    {nuc : Genesis.EigenformSoup.SoupNucleus}
    (s : Genesis.EigenformSoup.SoupState nuc) :
    (eigenformSoupToWitness s).level =
      fun fuel => Genesis.EigenformSoup.jRatchetLevel (Genesis.EigenformSoup.runSoupAux fuel s) := rfl

end JRatchet
end Bridges
end HeytingLean
