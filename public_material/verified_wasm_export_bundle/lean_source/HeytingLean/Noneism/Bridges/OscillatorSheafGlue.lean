import HeytingLean.Noneism.Bridges.OscillatorEquiv

/-!
# Noneism.Bridges.OscillatorSheafGlue

Bidirectional sheaf-glue witnesses among all 13 primordial oscillator carriers.
-/

namespace HeytingLean
namespace Noneism
namespace Bridges

open HeytingLean.Noneism
open HeytingLean.Information

/-- Two oscillators glue iff there exists a `PrimordialTension`-preserving equivalence. -/
def OscillatorsGlue (α β : Type*) [PrimordialTension α] [PrimordialTension β] : Prop :=
  ∃ _m : OscillatorMorphism α β, True

/-- Any two `PrimordialTension` carriers glue via the Bool hub. -/
theorem oscillatorsGlue_of_morphisms_via_bool
    {α β : Type*} [PrimordialTension α] [PrimordialTension β]
    (fα : OscillatorMorphism Bool α) (fβ : OscillatorMorphism Bool β) :
    OscillatorsGlue α β := by
  refine ⟨OscillatorMorphism.trans (OscillatorMorphism.symm fα) fβ, trivial⟩

private def glue_pair {α β : Type*} [PrimordialTension α] [PrimordialTension β]
    (fα : OscillatorMorphism Bool α) (fβ : OscillatorMorphism Bool β) :
    OscillatorsGlue α β ∧ OscillatorsGlue β α :=
  And.intro
    (oscillatorsGlue_of_morphisms_via_bool fα fβ)
    (oscillatorsGlue_of_morphisms_via_bool fβ fα)

abbrev m_bool : OscillatorMorphism Bool Bool := OscillatorMorphism.refl Bool
abbrev m_iterant : OscillatorMorphism Bool IterantPhase := morphism_bool_iterant
abbrev m_infostate : OscillatorMorphism Bool InfoState := morphism_bool_infostate
abbrev m_side : OscillatorMorphism Bool Side := morphism_bool_side
abbrev m_genesis : OscillatorMorphism Bool GamePolarity := morphism_bool_genesis
abbrev m_sphere : OscillatorMorphism Bool ZeroSphere := morphism_bool_sphere
abbrev m_star : OscillatorMorphism Bool StarPlayer := morphism_bool_star
abbrev m_euler : OscillatorMorphism Bool EulerRestriction := morphism_bool_euler
abbrev m_pregame : OscillatorMorphism Bool PreGameOscillatorState := morphism_bool_pregame
abbrev m_clifford : OscillatorMorphism Bool CliffordGrade := morphism_bool_clifford
abbrev m_linear : OscillatorMorphism Bool LinearPolarity := morphism_bool_linear
abbrev m_dialectica : OscillatorMorphism Bool DialecticaRole := morphism_bool_dialectica
abbrev m_ortho : OscillatorMorphism Bool OrthoPolarity := morphism_bool_ortho


theorem thm_sheaf_glue_oscillator_bool_to_oscillator_iterant :
    OscillatorsGlue Bool IterantPhase :=
  (glue_pair m_bool m_iterant).1

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_bool :
    OscillatorsGlue IterantPhase Bool :=
  (glue_pair m_bool m_iterant).2

theorem thm_sheaf_glue_oscillator_bool_to_oscillator_infostate :
    OscillatorsGlue Bool InfoState :=
  (glue_pair m_bool m_infostate).1

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_bool :
    OscillatorsGlue InfoState Bool :=
  (glue_pair m_bool m_infostate).2

theorem thm_sheaf_glue_oscillator_bool_to_oscillator_side :
    OscillatorsGlue Bool Side :=
  (glue_pair m_bool m_side).1

theorem thm_sheaf_glue_oscillator_side_to_oscillator_bool :
    OscillatorsGlue Side Bool :=
  (glue_pair m_bool m_side).2

theorem thm_sheaf_glue_oscillator_bool_to_oscillator_genesis :
    OscillatorsGlue Bool GamePolarity :=
  (glue_pair m_bool m_genesis).1

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_bool :
    OscillatorsGlue GamePolarity Bool :=
  (glue_pair m_bool m_genesis).2

theorem thm_sheaf_glue_oscillator_bool_to_oscillator_sphere :
    OscillatorsGlue Bool ZeroSphere :=
  (glue_pair m_bool m_sphere).1

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_bool :
    OscillatorsGlue ZeroSphere Bool :=
  (glue_pair m_bool m_sphere).2

theorem thm_sheaf_glue_oscillator_bool_to_oscillator_star :
    OscillatorsGlue Bool StarPlayer :=
  (glue_pair m_bool m_star).1

theorem thm_sheaf_glue_oscillator_star_to_oscillator_bool :
    OscillatorsGlue StarPlayer Bool :=
  (glue_pair m_bool m_star).2

theorem thm_sheaf_glue_oscillator_bool_to_oscillator_euler :
    OscillatorsGlue Bool EulerRestriction :=
  (glue_pair m_bool m_euler).1

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_bool :
    OscillatorsGlue EulerRestriction Bool :=
  (glue_pair m_bool m_euler).2

theorem thm_sheaf_glue_oscillator_bool_to_oscillator_pregame :
    OscillatorsGlue Bool PreGameOscillatorState :=
  (glue_pair m_bool m_pregame).1

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_bool :
    OscillatorsGlue PreGameOscillatorState Bool :=
  (glue_pair m_bool m_pregame).2

theorem thm_sheaf_glue_oscillator_bool_to_oscillator_clifford :
    OscillatorsGlue Bool CliffordGrade :=
  (glue_pair m_bool m_clifford).1

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_bool :
    OscillatorsGlue CliffordGrade Bool :=
  (glue_pair m_bool m_clifford).2

theorem thm_sheaf_glue_oscillator_bool_to_oscillator_linear :
    OscillatorsGlue Bool LinearPolarity :=
  (glue_pair m_bool m_linear).1

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_bool :
    OscillatorsGlue LinearPolarity Bool :=
  (glue_pair m_bool m_linear).2

theorem thm_sheaf_glue_oscillator_bool_to_oscillator_dialectica :
    OscillatorsGlue Bool DialecticaRole :=
  (glue_pair m_bool m_dialectica).1

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_bool :
    OscillatorsGlue DialecticaRole Bool :=
  (glue_pair m_bool m_dialectica).2

theorem thm_sheaf_glue_oscillator_bool_to_oscillator_ortho :
    OscillatorsGlue Bool OrthoPolarity :=
  (glue_pair m_bool m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_bool :
    OscillatorsGlue OrthoPolarity Bool :=
  (glue_pair m_bool m_ortho).2

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_infostate :
    OscillatorsGlue IterantPhase InfoState :=
  (glue_pair m_iterant m_infostate).1

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_iterant :
    OscillatorsGlue InfoState IterantPhase :=
  (glue_pair m_iterant m_infostate).2

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_side :
    OscillatorsGlue IterantPhase Side :=
  (glue_pair m_iterant m_side).1

theorem thm_sheaf_glue_oscillator_side_to_oscillator_iterant :
    OscillatorsGlue Side IterantPhase :=
  (glue_pair m_iterant m_side).2

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_genesis :
    OscillatorsGlue IterantPhase GamePolarity :=
  (glue_pair m_iterant m_genesis).1

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_iterant :
    OscillatorsGlue GamePolarity IterantPhase :=
  (glue_pair m_iterant m_genesis).2

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_sphere :
    OscillatorsGlue IterantPhase ZeroSphere :=
  (glue_pair m_iterant m_sphere).1

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_iterant :
    OscillatorsGlue ZeroSphere IterantPhase :=
  (glue_pair m_iterant m_sphere).2

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_star :
    OscillatorsGlue IterantPhase StarPlayer :=
  (glue_pair m_iterant m_star).1

theorem thm_sheaf_glue_oscillator_star_to_oscillator_iterant :
    OscillatorsGlue StarPlayer IterantPhase :=
  (glue_pair m_iterant m_star).2

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_euler :
    OscillatorsGlue IterantPhase EulerRestriction :=
  (glue_pair m_iterant m_euler).1

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_iterant :
    OscillatorsGlue EulerRestriction IterantPhase :=
  (glue_pair m_iterant m_euler).2

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_pregame :
    OscillatorsGlue IterantPhase PreGameOscillatorState :=
  (glue_pair m_iterant m_pregame).1

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_iterant :
    OscillatorsGlue PreGameOscillatorState IterantPhase :=
  (glue_pair m_iterant m_pregame).2

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_clifford :
    OscillatorsGlue IterantPhase CliffordGrade :=
  (glue_pair m_iterant m_clifford).1

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_iterant :
    OscillatorsGlue CliffordGrade IterantPhase :=
  (glue_pair m_iterant m_clifford).2

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_linear :
    OscillatorsGlue IterantPhase LinearPolarity :=
  (glue_pair m_iterant m_linear).1

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_iterant :
    OscillatorsGlue LinearPolarity IterantPhase :=
  (glue_pair m_iterant m_linear).2

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_dialectica :
    OscillatorsGlue IterantPhase DialecticaRole :=
  (glue_pair m_iterant m_dialectica).1

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_iterant :
    OscillatorsGlue DialecticaRole IterantPhase :=
  (glue_pair m_iterant m_dialectica).2

theorem thm_sheaf_glue_oscillator_iterant_to_oscillator_ortho :
    OscillatorsGlue IterantPhase OrthoPolarity :=
  (glue_pair m_iterant m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_iterant :
    OscillatorsGlue OrthoPolarity IterantPhase :=
  (glue_pair m_iterant m_ortho).2

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_side :
    OscillatorsGlue InfoState Side :=
  (glue_pair m_infostate m_side).1

theorem thm_sheaf_glue_oscillator_side_to_oscillator_infostate :
    OscillatorsGlue Side InfoState :=
  (glue_pair m_infostate m_side).2

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_genesis :
    OscillatorsGlue InfoState GamePolarity :=
  (glue_pair m_infostate m_genesis).1

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_infostate :
    OscillatorsGlue GamePolarity InfoState :=
  (glue_pair m_infostate m_genesis).2

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_sphere :
    OscillatorsGlue InfoState ZeroSphere :=
  (glue_pair m_infostate m_sphere).1

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_infostate :
    OscillatorsGlue ZeroSphere InfoState :=
  (glue_pair m_infostate m_sphere).2

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_star :
    OscillatorsGlue InfoState StarPlayer :=
  (glue_pair m_infostate m_star).1

theorem thm_sheaf_glue_oscillator_star_to_oscillator_infostate :
    OscillatorsGlue StarPlayer InfoState :=
  (glue_pair m_infostate m_star).2

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_euler :
    OscillatorsGlue InfoState EulerRestriction :=
  (glue_pair m_infostate m_euler).1

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_infostate :
    OscillatorsGlue EulerRestriction InfoState :=
  (glue_pair m_infostate m_euler).2

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_pregame :
    OscillatorsGlue InfoState PreGameOscillatorState :=
  (glue_pair m_infostate m_pregame).1

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_infostate :
    OscillatorsGlue PreGameOscillatorState InfoState :=
  (glue_pair m_infostate m_pregame).2

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_clifford :
    OscillatorsGlue InfoState CliffordGrade :=
  (glue_pair m_infostate m_clifford).1

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_infostate :
    OscillatorsGlue CliffordGrade InfoState :=
  (glue_pair m_infostate m_clifford).2

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_linear :
    OscillatorsGlue InfoState LinearPolarity :=
  (glue_pair m_infostate m_linear).1

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_infostate :
    OscillatorsGlue LinearPolarity InfoState :=
  (glue_pair m_infostate m_linear).2

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_dialectica :
    OscillatorsGlue InfoState DialecticaRole :=
  (glue_pair m_infostate m_dialectica).1

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_infostate :
    OscillatorsGlue DialecticaRole InfoState :=
  (glue_pair m_infostate m_dialectica).2

theorem thm_sheaf_glue_oscillator_infostate_to_oscillator_ortho :
    OscillatorsGlue InfoState OrthoPolarity :=
  (glue_pair m_infostate m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_infostate :
    OscillatorsGlue OrthoPolarity InfoState :=
  (glue_pair m_infostate m_ortho).2

theorem thm_sheaf_glue_oscillator_side_to_oscillator_genesis :
    OscillatorsGlue Side GamePolarity :=
  (glue_pair m_side m_genesis).1

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_side :
    OscillatorsGlue GamePolarity Side :=
  (glue_pair m_side m_genesis).2

theorem thm_sheaf_glue_oscillator_side_to_oscillator_sphere :
    OscillatorsGlue Side ZeroSphere :=
  (glue_pair m_side m_sphere).1

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_side :
    OscillatorsGlue ZeroSphere Side :=
  (glue_pair m_side m_sphere).2

theorem thm_sheaf_glue_oscillator_side_to_oscillator_star :
    OscillatorsGlue Side StarPlayer :=
  (glue_pair m_side m_star).1

theorem thm_sheaf_glue_oscillator_star_to_oscillator_side :
    OscillatorsGlue StarPlayer Side :=
  (glue_pair m_side m_star).2

theorem thm_sheaf_glue_oscillator_side_to_oscillator_euler :
    OscillatorsGlue Side EulerRestriction :=
  (glue_pair m_side m_euler).1

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_side :
    OscillatorsGlue EulerRestriction Side :=
  (glue_pair m_side m_euler).2

theorem thm_sheaf_glue_oscillator_side_to_oscillator_pregame :
    OscillatorsGlue Side PreGameOscillatorState :=
  (glue_pair m_side m_pregame).1

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_side :
    OscillatorsGlue PreGameOscillatorState Side :=
  (glue_pair m_side m_pregame).2

theorem thm_sheaf_glue_oscillator_side_to_oscillator_clifford :
    OscillatorsGlue Side CliffordGrade :=
  (glue_pair m_side m_clifford).1

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_side :
    OscillatorsGlue CliffordGrade Side :=
  (glue_pair m_side m_clifford).2

theorem thm_sheaf_glue_oscillator_side_to_oscillator_linear :
    OscillatorsGlue Side LinearPolarity :=
  (glue_pair m_side m_linear).1

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_side :
    OscillatorsGlue LinearPolarity Side :=
  (glue_pair m_side m_linear).2

theorem thm_sheaf_glue_oscillator_side_to_oscillator_dialectica :
    OscillatorsGlue Side DialecticaRole :=
  (glue_pair m_side m_dialectica).1

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_side :
    OscillatorsGlue DialecticaRole Side :=
  (glue_pair m_side m_dialectica).2

theorem thm_sheaf_glue_oscillator_side_to_oscillator_ortho :
    OscillatorsGlue Side OrthoPolarity :=
  (glue_pair m_side m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_side :
    OscillatorsGlue OrthoPolarity Side :=
  (glue_pair m_side m_ortho).2

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_sphere :
    OscillatorsGlue GamePolarity ZeroSphere :=
  (glue_pair m_genesis m_sphere).1

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_genesis :
    OscillatorsGlue ZeroSphere GamePolarity :=
  (glue_pair m_genesis m_sphere).2

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_star :
    OscillatorsGlue GamePolarity StarPlayer :=
  (glue_pair m_genesis m_star).1

theorem thm_sheaf_glue_oscillator_star_to_oscillator_genesis :
    OscillatorsGlue StarPlayer GamePolarity :=
  (glue_pair m_genesis m_star).2

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_euler :
    OscillatorsGlue GamePolarity EulerRestriction :=
  (glue_pair m_genesis m_euler).1

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_genesis :
    OscillatorsGlue EulerRestriction GamePolarity :=
  (glue_pair m_genesis m_euler).2

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_pregame :
    OscillatorsGlue GamePolarity PreGameOscillatorState :=
  (glue_pair m_genesis m_pregame).1

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_genesis :
    OscillatorsGlue PreGameOscillatorState GamePolarity :=
  (glue_pair m_genesis m_pregame).2

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_clifford :
    OscillatorsGlue GamePolarity CliffordGrade :=
  (glue_pair m_genesis m_clifford).1

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_genesis :
    OscillatorsGlue CliffordGrade GamePolarity :=
  (glue_pair m_genesis m_clifford).2

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_linear :
    OscillatorsGlue GamePolarity LinearPolarity :=
  (glue_pair m_genesis m_linear).1

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_genesis :
    OscillatorsGlue LinearPolarity GamePolarity :=
  (glue_pair m_genesis m_linear).2

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_dialectica :
    OscillatorsGlue GamePolarity DialecticaRole :=
  (glue_pair m_genesis m_dialectica).1

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_genesis :
    OscillatorsGlue DialecticaRole GamePolarity :=
  (glue_pair m_genesis m_dialectica).2

theorem thm_sheaf_glue_oscillator_genesis_to_oscillator_ortho :
    OscillatorsGlue GamePolarity OrthoPolarity :=
  (glue_pair m_genesis m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_genesis :
    OscillatorsGlue OrthoPolarity GamePolarity :=
  (glue_pair m_genesis m_ortho).2

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_star :
    OscillatorsGlue ZeroSphere StarPlayer :=
  (glue_pair m_sphere m_star).1

theorem thm_sheaf_glue_oscillator_star_to_oscillator_sphere :
    OscillatorsGlue StarPlayer ZeroSphere :=
  (glue_pair m_sphere m_star).2

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_euler :
    OscillatorsGlue ZeroSphere EulerRestriction :=
  (glue_pair m_sphere m_euler).1

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_sphere :
    OscillatorsGlue EulerRestriction ZeroSphere :=
  (glue_pair m_sphere m_euler).2

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_pregame :
    OscillatorsGlue ZeroSphere PreGameOscillatorState :=
  (glue_pair m_sphere m_pregame).1

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_sphere :
    OscillatorsGlue PreGameOscillatorState ZeroSphere :=
  (glue_pair m_sphere m_pregame).2

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_clifford :
    OscillatorsGlue ZeroSphere CliffordGrade :=
  (glue_pair m_sphere m_clifford).1

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_sphere :
    OscillatorsGlue CliffordGrade ZeroSphere :=
  (glue_pair m_sphere m_clifford).2

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_linear :
    OscillatorsGlue ZeroSphere LinearPolarity :=
  (glue_pair m_sphere m_linear).1

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_sphere :
    OscillatorsGlue LinearPolarity ZeroSphere :=
  (glue_pair m_sphere m_linear).2

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_dialectica :
    OscillatorsGlue ZeroSphere DialecticaRole :=
  (glue_pair m_sphere m_dialectica).1

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_sphere :
    OscillatorsGlue DialecticaRole ZeroSphere :=
  (glue_pair m_sphere m_dialectica).2

theorem thm_sheaf_glue_oscillator_sphere_to_oscillator_ortho :
    OscillatorsGlue ZeroSphere OrthoPolarity :=
  (glue_pair m_sphere m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_sphere :
    OscillatorsGlue OrthoPolarity ZeroSphere :=
  (glue_pair m_sphere m_ortho).2

theorem thm_sheaf_glue_oscillator_star_to_oscillator_euler :
    OscillatorsGlue StarPlayer EulerRestriction :=
  (glue_pair m_star m_euler).1

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_star :
    OscillatorsGlue EulerRestriction StarPlayer :=
  (glue_pair m_star m_euler).2

theorem thm_sheaf_glue_oscillator_star_to_oscillator_pregame :
    OscillatorsGlue StarPlayer PreGameOscillatorState :=
  (glue_pair m_star m_pregame).1

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_star :
    OscillatorsGlue PreGameOscillatorState StarPlayer :=
  (glue_pair m_star m_pregame).2

theorem thm_sheaf_glue_oscillator_star_to_oscillator_clifford :
    OscillatorsGlue StarPlayer CliffordGrade :=
  (glue_pair m_star m_clifford).1

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_star :
    OscillatorsGlue CliffordGrade StarPlayer :=
  (glue_pair m_star m_clifford).2

theorem thm_sheaf_glue_oscillator_star_to_oscillator_linear :
    OscillatorsGlue StarPlayer LinearPolarity :=
  (glue_pair m_star m_linear).1

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_star :
    OscillatorsGlue LinearPolarity StarPlayer :=
  (glue_pair m_star m_linear).2

theorem thm_sheaf_glue_oscillator_star_to_oscillator_dialectica :
    OscillatorsGlue StarPlayer DialecticaRole :=
  (glue_pair m_star m_dialectica).1

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_star :
    OscillatorsGlue DialecticaRole StarPlayer :=
  (glue_pair m_star m_dialectica).2

theorem thm_sheaf_glue_oscillator_star_to_oscillator_ortho :
    OscillatorsGlue StarPlayer OrthoPolarity :=
  (glue_pair m_star m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_star :
    OscillatorsGlue OrthoPolarity StarPlayer :=
  (glue_pair m_star m_ortho).2

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_pregame :
    OscillatorsGlue EulerRestriction PreGameOscillatorState :=
  (glue_pair m_euler m_pregame).1

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_euler :
    OscillatorsGlue PreGameOscillatorState EulerRestriction :=
  (glue_pair m_euler m_pregame).2

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_clifford :
    OscillatorsGlue EulerRestriction CliffordGrade :=
  (glue_pair m_euler m_clifford).1

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_euler :
    OscillatorsGlue CliffordGrade EulerRestriction :=
  (glue_pair m_euler m_clifford).2

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_linear :
    OscillatorsGlue EulerRestriction LinearPolarity :=
  (glue_pair m_euler m_linear).1

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_euler :
    OscillatorsGlue LinearPolarity EulerRestriction :=
  (glue_pair m_euler m_linear).2

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_dialectica :
    OscillatorsGlue EulerRestriction DialecticaRole :=
  (glue_pair m_euler m_dialectica).1

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_euler :
    OscillatorsGlue DialecticaRole EulerRestriction :=
  (glue_pair m_euler m_dialectica).2

theorem thm_sheaf_glue_oscillator_euler_to_oscillator_ortho :
    OscillatorsGlue EulerRestriction OrthoPolarity :=
  (glue_pair m_euler m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_euler :
    OscillatorsGlue OrthoPolarity EulerRestriction :=
  (glue_pair m_euler m_ortho).2

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_clifford :
    OscillatorsGlue PreGameOscillatorState CliffordGrade :=
  (glue_pair m_pregame m_clifford).1

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_pregame :
    OscillatorsGlue CliffordGrade PreGameOscillatorState :=
  (glue_pair m_pregame m_clifford).2

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_linear :
    OscillatorsGlue PreGameOscillatorState LinearPolarity :=
  (glue_pair m_pregame m_linear).1

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_pregame :
    OscillatorsGlue LinearPolarity PreGameOscillatorState :=
  (glue_pair m_pregame m_linear).2

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_dialectica :
    OscillatorsGlue PreGameOscillatorState DialecticaRole :=
  (glue_pair m_pregame m_dialectica).1

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_pregame :
    OscillatorsGlue DialecticaRole PreGameOscillatorState :=
  (glue_pair m_pregame m_dialectica).2

theorem thm_sheaf_glue_oscillator_pregame_to_oscillator_ortho :
    OscillatorsGlue PreGameOscillatorState OrthoPolarity :=
  (glue_pair m_pregame m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_pregame :
    OscillatorsGlue OrthoPolarity PreGameOscillatorState :=
  (glue_pair m_pregame m_ortho).2

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_linear :
    OscillatorsGlue CliffordGrade LinearPolarity :=
  (glue_pair m_clifford m_linear).1

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_clifford :
    OscillatorsGlue LinearPolarity CliffordGrade :=
  (glue_pair m_clifford m_linear).2

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_dialectica :
    OscillatorsGlue CliffordGrade DialecticaRole :=
  (glue_pair m_clifford m_dialectica).1

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_clifford :
    OscillatorsGlue DialecticaRole CliffordGrade :=
  (glue_pair m_clifford m_dialectica).2

theorem thm_sheaf_glue_oscillator_clifford_to_oscillator_ortho :
    OscillatorsGlue CliffordGrade OrthoPolarity :=
  (glue_pair m_clifford m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_clifford :
    OscillatorsGlue OrthoPolarity CliffordGrade :=
  (glue_pair m_clifford m_ortho).2

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_dialectica :
    OscillatorsGlue LinearPolarity DialecticaRole :=
  (glue_pair m_linear m_dialectica).1

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_linear :
    OscillatorsGlue DialecticaRole LinearPolarity :=
  (glue_pair m_linear m_dialectica).2

theorem thm_sheaf_glue_oscillator_linear_to_oscillator_ortho :
    OscillatorsGlue LinearPolarity OrthoPolarity :=
  (glue_pair m_linear m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_linear :
    OscillatorsGlue OrthoPolarity LinearPolarity :=
  (glue_pair m_linear m_ortho).2

theorem thm_sheaf_glue_oscillator_dialectica_to_oscillator_ortho :
    OscillatorsGlue DialecticaRole OrthoPolarity :=
  (glue_pair m_dialectica m_ortho).1

theorem thm_sheaf_glue_oscillator_ortho_to_oscillator_dialectica :
    OscillatorsGlue OrthoPolarity DialecticaRole :=
  (glue_pair m_dialectica m_ortho).2

end Bridges
end Noneism
end HeytingLean
