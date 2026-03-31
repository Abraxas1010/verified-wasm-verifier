import HeytingLean.EpistemicCalculus.Basic
import HeytingLean.EpistemicCalculus.Axioms

namespace HeytingLean.EpistemicCalculus

/--
No-go form: if fusion is inflationary (`E5`) and `unit` is also an upper bound,
the calculus collapses to a singleton, contradicting non-triviality.
-/
theorem no_stronglyConservative_of_unit_top
    (V : Type*) [EpistemicCalculus V] [StronglyConservative V]
    (hunitTop : ∀ x : V, x ≤ EpistemicCalculus.unit) : False := by
  rcases EpistemicCalculus.nontrivial (V := V) with ⟨a, b, hab⟩
  have hUnitLeA : EpistemicCalculus.unit ≤ a := by
    simpa [EpistemicCalculus.fusion_unit_left] using
      (StronglyConservative.no_decrease (V := V) (x := EpistemicCalculus.unit) (y := a))
  have hUnitLeB : EpistemicCalculus.unit ≤ b := by
    simpa [EpistemicCalculus.fusion_unit_left] using
      (StronglyConservative.no_decrease (V := V) (x := EpistemicCalculus.unit) (y := b))
  have ha : a = EpistemicCalculus.unit := le_antisymm (hunitTop a) hUnitLeA
  have hb : b = EpistemicCalculus.unit := le_antisymm (hunitTop b) hUnitLeB
  exact hab (ha.trans hb.symm)

/-- Closed calculi are fallible when each element is below its own residual witness. -/
theorem closed_implies_fallible_of_self_below_ihom
    (V : Type*) [EpistemicCalculus V] [Closed V]
    (hdiag : ∀ x y : V, x ≤ Closed.ihom (Closed.ihom x y) y) :
    Fallible V := by
  refine ⟨?_⟩
  intro x y
  refine ⟨Closed.ihom x y, ?_⟩
  exact (Closed.adjunction x (Closed.ihom x y) y).2 (hdiag x y)

/--
Quantale-style bridge shape:
if closedness gives revisability and revisability reconstructs closedness,
the two principles are equivalent.
-/
theorem closed_iff_fallible_of_quantale
    (V : Type*) [EpistemicCalculus V]
    (hClosedToFallible : Nonempty (Closed V) → Nonempty (Fallible V))
    (hFallibleToClosed : Nonempty (Fallible V) → Nonempty (Closed V)) :
    Nonempty (Closed V) ↔ Nonempty (Fallible V) := by
  constructor
  · exact hClosedToFallible
  · exact hFallibleToClosed

/--
On a total order (expressed directly as comparability in the calculus order)
with `unit` as top and idempotent fusion, fusion matches the `if`-minimum.
-/
theorem idempotent_is_min
    (V : Type*) [EpistemicCalculus V]
    (hid : ∀ x : V, x fus x = x)
    (unit_is_top : ∀ x : V, x ≤ EpistemicCalculus.unit)
    (htotal : ∀ x y : V, x ≤ y ∨ y ≤ x)
    [DecidableRel (fun a b : V => a ≤ b)] :
    ∀ x y : V, x fus y = (if x ≤ y then x else y) := by
  have case_le : ∀ {a b : V}, a ≤ b → a fus b = a := by
    intro a b hab
    have hLower : a ≤ a fus b := by
      have hmono : a fus a ≤ a fus b := fusion_mono_right (x := a) hab
      simp [hid a] at hmono
      exact hmono
    have hUpper : a fus b ≤ a := by
      have hmono : a fus b ≤ a fus EpistemicCalculus.unit :=
        fusion_mono_right (x := a) (unit_is_top b)
      simpa [fusion_unit_right] using hmono
    exact le_antisymm hUpper hLower
  intro x y
  cases htotal x y with
  | inl hxy =>
      simp [hxy, case_le (a := x) (b := y) hxy]
  | inr hyx =>
      have hFusion : x fus y = y := by
        simpa [EpistemicCalculus.fusion_comm] using (case_le (a := y) (b := x) hyx)
      by_cases hxy : x ≤ y
      · have hEq : x = y := le_antisymm hxy hyx
        subst hEq
        simpa using hid x
      · simp [hxy, hFusion]

end HeytingLean.EpistemicCalculus
