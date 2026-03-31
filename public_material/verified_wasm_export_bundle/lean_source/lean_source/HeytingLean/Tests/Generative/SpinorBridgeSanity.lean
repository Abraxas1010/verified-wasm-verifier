import HeytingLean.Generative.SpinorBridge

open HeytingLean.Generative
open HeytingLean.Generative.SpinorBridge

#check pauliZ_sq
#check involutivity_is_double_cover
#check clebsch_gordan_dimension
#check spatial_dimension_eq_su2_generator_count
#check complexification_is_barrier
#check non_boolean_is_aperiodic

example : pauliZ * pauliZ = 1 :=
  pauliZ_sq

example :
    stepOnSupport noneistAxis
      (stepOnSupport noneistAxis ⟨noneistAxis.state₁, Or.inl rfl⟩) =
      ⟨noneistAxis.state₁, Or.inl rfl⟩ := by
  simpa using involutivity_is_double_cover noneistAxis ⟨noneistAxis.state₁, Or.inl rfl⟩

example : level2.dim = Fintype.card SU2Generator :=
  spatial_dimension_eq_su2_generator_count

example :
    Fintype.card SL2CGenerator = 2 * Fintype.card SU2Generator :=
  complexification_doubles_generators
