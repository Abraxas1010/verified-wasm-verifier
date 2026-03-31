import HeytingLean.Physics.FreeWill.Directions
import HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerDeep.Basic
import HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerDeep.KochenSpecker

set_option autoImplicit false

namespace HeytingLean.Physics.FreeWill

open HeytingLean.Noneism.Contextuality.KochenSpeckerDeep

abbrev Dir : Type := MeasurementDirection
abbrev Orth : Dir → Dir → Prop := IsPerpendicular
abbrev PeresFrame : Type := Frame Dir Orth

/-- Canonical orthogonal frame from the deep KS development (`x ⟂ y ⟂ z`). -/
noncomputable def xyzFrame : PeresFrame :=
  ⟨x, y, z, perp_xyz.1, perp_xyz.2.2, perp_xyz.2.1⟩

noncomputable instance : Inhabited PeresFrame := ⟨xyzFrame⟩

@[simp] def boolToSpin : Bool → SpinMeasurement
  | false => SpinMeasurement.zero
  | true => SpinMeasurement.one

@[simp] theorem boolToSpin_false : boolToSpin false = SpinMeasurement.zero := rfl
@[simp] theorem boolToSpin_true : boolToSpin true = SpinMeasurement.one := rfl

private theorem validTriples_of_exactlyOneFalse {a b c : Bool}
    (h : ExactlyOneFalse a b c) :
    [boolToSpin a, boolToSpin b, boolToSpin c] ∈ ValidThriples := by
  rcases h with h0 | h1 | h2
  · rcases h0 with ⟨ha, hb, hc⟩
    simp [ValidThriples, boolToSpin, ha, hb, hc]
  · rcases h1 with ⟨ha, hb, hc⟩
    simp [ValidThriples, boolToSpin, ha, hb, hc]
  · rcases h2 with ⟨ha, hb, hc⟩
    simp [ValidThriples, boolToSpin, ha, hb, hc]

private theorem isOneZeroOne_of_is101 (θ : Dir → Bool)
    (hθ : Is101 Orth θ) :
    IsOneZeroOneFunc (fun d => boolToSpin (θ d)) := by
  intro d1 d2 d3 hperp
  have hframe : ExactlyOneFalse (θ d1) (θ d2) (θ d3) := by
    exact hθ ⟨d1, d2, d3, hperp.1, hperp.2.2, hperp.2.1⟩
  exact validTriples_of_exactlyOneFalse hframe

/-- Axiom-free Peres-33 endpoint via the in-repo Kochen-Specker proof artifact. -/
theorem no101_peres33 : ¬ ∃ θ : Dir → Bool, Is101 Orth θ := by
  intro h
  rcases h with ⟨θ, hθ⟩
  let f : OneZeroOneFunc := ⟨fun d => boolToSpin (θ d), isOneZeroOne_of_is101 θ hθ⟩
  exact kochen_specker f

end HeytingLean.Physics.FreeWill
