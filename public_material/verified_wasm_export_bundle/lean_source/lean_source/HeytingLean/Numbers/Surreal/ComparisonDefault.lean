import Mathlib.Order.GaloisConnection.Basic
import HeytingLean.Numbers.Surreal.ClosureReentry
import HeytingLean.Numbers.Surreal.ComparisonCore

/-!
# Default identity diamond for Surreals

We choose the Option-A nucleus fixed points as the “direct” right-leg bottom:
  Ωₗ := Ω_core
and define
  f_id : Set PreGame → Ωₗ       by closing then wrapping,
  g_id : Ωₗ → Set PreGame       by subtype projection.

Then `comparisonCore f_id g_id gc_id` has `act = R_core.act`, so the
comparison closure equals the Option-A nucleus by construction.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore

/-! ### Option-A nucleus and its Ω -/

def R_core : Nucleus (Set SurrealCore.PreGame) :=
  closureCore

-- Fixed points of R_core as a simple subtype (avoids sublocale APIs here).
abbrev Ω_core := {S : Set SurrealCore.PreGame // R_core S = S}

/-! ### Identity right-leg and Galois connection -/

abbrev Ωₗ := Ω_core

def f_id : Set SurrealCore.PreGame → Ωₗ :=
  fun S => ⟨R_core S, R_core.idempotent S⟩

def g_id : Ωₗ → Set SurrealCore.PreGame := Subtype.val

-- Helper: elements of Ωₗ are fixed by `R_core`.
lemma fixed_coe (u : Ωₗ) : R_core (u : Set SurrealCore.PreGame) = (u : Set SurrealCore.PreGame) := by
  simpa using u.property

lemma gc_id : GaloisConnection f_id g_id := by
  intro S u
  -- f_id S ≤ u  ↔  R S ≤ u  ↔  S ≤ u  (since S ≤ R S and u is fixed)
  change R_core S ≤ (u : Set SurrealCore.PreGame) ↔ S ≤ (u : Set SurrealCore.PreGame)
  constructor
  · intro h; exact (le_trans ((R_core.le_apply' S)) h)
  · intro h
    have h' := (Nucleus.monotone (n := R_core)) h
    simpa [fixed_coe (u := u)] using h'

/-! ### Comparison closure equals the Option-A nucleus -/

theorem comparison_is_identity :
    (comparisonCore f_id g_id gc_id).act = (R_core : Set SurrealCore.PreGame → Set SurrealCore.PreGame) := rfl

/-! ### Adjunction rewrite lemmas and universal property -/

@[simp] lemma gc_id_u_l (S : Set SurrealCore.PreGame) :
    g_id (f_id S) = R_core S := rfl

@[simp] lemma gc_id_l_u (u : Ωₗ) :
    f_id (g_id u) = u := by
  apply Subtype.ext
  simp [f_id, g_id, fixed_coe]

-- Kernel/reflector universal property: any h commuting with R_core factors uniquely through Ωₗ.
def factor (h : Set SurrealCore.PreGame → Ωₗ)
    (_hh : ∀ S, h (R_core S) = h S) : Ωₗ → Ωₗ :=
  fun u => h (g_id u)

lemma factor_commutes (h : Set SurrealCore.PreGame → Ωₗ)
    (hh : ∀ S, h (R_core S) = h S) (S : Set SurrealCore.PreGame) :
    factor h hh (f_id S) = h S := by
  unfold factor
  simp [f_id, g_id, hh]

lemma factor_unique (h : Set SurrealCore.PreGame → Ωₗ)
    (hh : ∀ S, h (R_core S) = h S)
    (k : Ωₗ → Ωₗ)
    (hk : ∀ S, k (f_id S) = h S) :
    k = factor h hh := by
  funext u
  have : u = f_id (g_id u) := (gc_id_l_u (u := u)).symm
  simpa [factor] using congrArg k this ▸ hk (g_id u)

-- Trivial kernel-nucleus identity lemma in the identity setup.
lemma kernel_nucleus_id :
    (comparisonCore f_id g_id gc_id).act = (R_core : Set SurrealCore.PreGame → Set SurrealCore.PreGame) := rfl

end Surreal
end Numbers
end HeytingLean
