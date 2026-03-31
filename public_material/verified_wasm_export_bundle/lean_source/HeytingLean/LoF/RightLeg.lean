import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Nucleus
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.BooleanAlgebra
import HeytingLean.Numbers.Surreal.ComparisonCore
import HeytingLean.Numbers.Surreal.Nucleus
import HeytingLean.Numbers.SurrealCore

/-!
# Parametric LoF right leg

Abstracts the right-leg (LoF) bottom as a complete lattice with a nucleus `R_dir`
and an interpretation of surreal sets into that carrier. A single additional law
(`close_preserves_supr`) suffices to synthesize a Galois connection and build the
comparison nucleus/factor without relying on sublocale lattice objects.
-/

namespace HeytingLean
namespace LoF

universe u v

open Classical
open Set
open Function (fixedPoints)
open HeytingLean.Numbers.SurrealCore

structure RightLeg (Carrier : Type v) [CompleteLattice Carrier] where
  R_dir   : Nucleus Carrier
  interp  : Set PreGame → Carrier
  interp_mono : Monotone interp
  /-- Key law: closure-after-interpretation distributes over arbitrary unions. -/
  close_preserves_sSup :
    ∀ (U : Set (Set PreGame)),
      R_dir (interp (sSup U)) = iSup (fun S : U => R_dir (interp S.1))

namespace RightLeg

variable {Carrier : Type v} [CompleteLattice Carrier]
variable (RL : RightLeg Carrier)

abbrev Ω_ℓ (RL : RightLeg Carrier) : Type v :=
  fixedPoints RL.R_dir.toClosureOperator.toOrderHom

/-- Underlying carrier of the meet of two fixed points is obtained by
closing the ambient meet. -/
@[simp] lemma coe_inf (RL : RightLeg Carrier)
    (x y : Ω_ℓ RL) :
    ((x ⊓ y : Ω_ℓ RL) : Carrier) =
      RL.R_dir ((x : Carrier) ⊓ (y : Carrier)) := by
  classical
  apply le_antisymm
  · -- meet in Ω lies below each argument; chaining with extensivity of the
    -- nucleus yields the desired carrier inequality.
    have hx : ((x ⊓ y : Ω_ℓ RL) : Carrier) ≤ (x : Carrier) := by
      change x ⊓ y ≤ x
      exact inf_le_left
    have hy : ((x ⊓ y : Ω_ℓ RL) : Carrier) ≤ (y : Carrier) := by
      change x ⊓ y ≤ y
      exact inf_le_right
    have hxy : ((x ⊓ y : Ω_ℓ RL) : Carrier)
        ≤ (x : Carrier) ⊓ (y : Carrier) := le_inf hx hy
    have hcl : (x : Carrier) ⊓ (y : Carrier) ≤
        RL.R_dir ((x : Carrier) ⊓ (y : Carrier)) := by
      simpa using (Nucleus.le_apply (n := RL.R_dir)
        (x := (x : Carrier) ⊓ (y : Carrier)))
    exact hxy.trans hcl
  · -- closing the ambient meet is itself a fixed point that bounds both
    -- arguments, hence lies below their meet in Ω.
    change RL.R_dir ((x : Carrier) ⊓ (y : Carrier)) ≤
      ((x ⊓ y : Ω_ℓ RL) : Carrier)
    set z : Carrier := RL.R_dir ((x : Carrier) ⊓ (y : Carrier)) with hz_def
    have hz_fix : RL.R_dir z = z := by
      calc
        RL.R_dir z
            = RL.R_dir (RL.R_dir ((x : Carrier) ⊓ (y : Carrier))) := by
                simp [hz_def]
        _ = RL.R_dir ((x : Carrier) ⊓ (y : Carrier)) :=
              RL.R_dir.idempotent _
        _ = z := by
                simp [hz_def]
    have hx_fix : RL.R_dir (x : Carrier) = (x : Carrier) :=
      Function.IsFixedPt.eq x.property
    have hy_fix : RL.R_dir (y : Carrier) = (y : Carrier) :=
      Function.IsFixedPt.eq y.property
    have hz_le_x : z ≤ (x : Carrier) := by
      have : ((x : Carrier) ⊓ (y : Carrier)) ≤ (x : Carrier) := inf_le_left
      have hz := RL.R_dir.monotone this
      have hz' : z ≤ RL.R_dir (x : Carrier) := by
        exact hz_def.symm ▸ hz
      exact hx_fix ▸ hz'
    have hz_le_y : z ≤ (y : Carrier) := by
      have : ((x : Carrier) ⊓ (y : Carrier)) ≤ (y : Carrier) := inf_le_right
      have hz := RL.R_dir.monotone this
      have hz' : z ≤ RL.R_dir (y : Carrier) := by
        exact hz_def.symm ▸ hz
      exact hy_fix ▸ hz'
    have hz_le_inf : (⟨z, hz_fix⟩ : Ω_ℓ RL) ≤ x ⊓ y :=
      le_inf hz_le_x hz_le_y
    have hz_le_inf' : z ≤ ((x ⊓ y : Ω_ℓ RL) : Carrier) := by
      change ((⟨z, hz_fix⟩ : Ω_ℓ RL) : Carrier) ≤ ((x ⊓ y : Ω_ℓ RL) : Carrier)
      exact hz_le_inf
    exact hz_le_inf'

/-- Left adjoint: close (under `R_dir`) after interpreting, then wrap. -/
def f (RL : RightLeg Carrier) (S : Set PreGame) : Ω_ℓ RL :=
  ⟨ RL.R_dir (RL.interp S), RL.R_dir.idempotent _ ⟩

/-- Right adjoint as the supremum of all sets whose image under `f` lies below `y`. -/
def g (RL : RightLeg Carrier) (y : Ω_ℓ RL) : Set PreGame :=
  sSup { S : Set PreGame | RL.f S ≤ y }

lemma f_monotone (RL : RightLeg Carrier) : Monotone (f RL) := by
  intro S T hST
  change RL.R_dir (RL.interp S) ≤ RL.R_dir (RL.interp T)
  exact (RL.R_dir.monotone) (RL.interp_mono hST)

/-- Galois connection `f ⊣ g`. -/
lemma gc (RL : RightLeg Carrier) : GaloisConnection (f RL) (g RL) := by
  intro a y
  constructor
  · intro h
    -- `a` is a member of the generating set; hence `a ≤ sSup {S | f S ≤ y}`
    exact le_sSup_of_le (by simpa using h) le_rfl
  · intro h
    -- Show `RL.f a ≤ y` using monotonicity + `close_preserves_iSup` and `iSup_le`.
    -- Monotone step: f a ≤ f (g y)
    have h1 : f RL a ≤ f RL (g RL y) := (f_monotone RL) h
    -- Use the sSup-preservation law on the family `U := {S | f S ≤ y}`.
    let U : Set (Set PreGame) := { S | RL.f S ≤ y }
    have hx : RL.R_dir (RL.interp (sSup U)) =
        iSup (fun u : {S // RL.f S ≤ y} => RL.R_dir (RL.interp u.1)) := by
      simpa [U] using (RL.close_preserves_sSup U)
    -- Bound `f (g y)` by `y` using `iSup_le` over the generating set.
    have h2 : f RL (g RL y) ≤ y := by
      -- unwrap to carriers and rewrite via `hx`
      change RL.R_dir (RL.interp (sSup U)) ≤ (y : Carrier)
      -- bound each generator by its witness `u.2 : f u.1 ≤ y`, via a `calc` with `hx`
      calc
        RL.R_dir (RL.interp (sSup U))
            = iSup (fun u : {S // RL.f S ≤ y} => (RL.R_dir (RL.interp u.1) : Carrier)) := by
                simpa [hx]
        _ ≤ (y : Carrier) := by
                refine iSup_le ?_;
                intro u; simpa [f] using (u.2)
    exact le_trans h1 h2

/-- Comparison nucleus: Rᶜ := g ∘ f on `Set PreGame`. -/
def R_comp (RL : RightLeg Carrier) : HeytingLean.LoF.ClosureCore (Set PreGame) :=
  HeytingLean.Numbers.Surreal.comparisonCore (f := f RL) (g := g RL) (gc := gc RL)

abbrev Ω_comp (RL : RightLeg Carrier) : Type := (R_comp RL).Omega

/-- Factor map from Ω_{Rᶜ} to Ω_ℓ. -/
def factor (RL : RightLeg Carrier) : Ω_comp RL → Ω_ℓ RL :=
  fun u => f RL (u : Set PreGame)

/-- Pointwise commuting lemma (by construction). -/
lemma f_le_factor_pointwise (RL : RightLeg Carrier) (S : Set PreGame) :
  f RL S ≤ factor RL ⟨ (R_comp RL).act S, (R_comp RL).idempotent S ⟩ := by
  -- `S ≤ R_comp.act S` by extensivity of the closure core
  have hext : S ≤ (R_comp RL).act S := (R_comp RL).le_apply S
  -- Monotonicity of f gives the result
  simpa using (f_monotone RL) hext

end RightLeg
end LoF
end HeytingLean
