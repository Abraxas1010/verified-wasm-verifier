import HeytingLean.ModalCategorySets.Propositional.Frames
import HeytingLean.ModalCategorySets.Validities.S4Universal
import HeytingLean.ModalCategorySets.Validities.GrzFinite

namespace HeytingLean.ModalCategorySets.Validities

open HeytingLean.ModalCategorySets.Propositional

universe u v

/-- `.2` is valid on directed frames. -/
theorem axiomDot2_valid_of_directed {W : Type u} {α : Type v} {F : Frame W}
    (hDir : ∀ w u v, F.rel w u → F.rel w v → ∃ z, F.rel u z ∧ F.rel v z) (p : α) :
    F.Valid (axiomDot2 p) := by
  intro val w hDiaBox v hwv
  rcases hDiaBox with ⟨u, hwu, huBox⟩
  rcases hDir w u v hwu hwv with ⟨z, huz, hvz⟩
  exact Exists.intro z (And.intro hvz (huBox z huz))

/-- The control-core axiom package `T + 4 + .2`. -/
def ValidatesS4Dot2 {W : Type u} (F : Frame W) : Prop :=
  ∀ {α : Type v} (p : α), F.Valid (axiomT p) ∧ F.Valid (axiom4 p) ∧ F.Valid (axiomDot2 p)

/-- The finite lower-bound control package used before full `Grz.2` completeness. -/
def ValidatesGrzDot2Core {W : Type u} (F : Frame W) : Prop :=
  ∀ {α : Type v} (p : α),
    F.Valid (axiomT p) ∧ F.Valid (axiom4 p) ∧ F.Valid (axiomDot2 p) ∧ F.Valid (axiomGrz p)

theorem validatesS4Dot2_of_reflexive_transitive_directed {W : Type u} (F : Frame W)
    (hRefl : Reflexive F) (hTrans : Transitive F)
    (hDir : ∀ w u v, F.rel w u → F.rel w v → ∃ z, F.rel u z ∧ F.rel v z) :
    ValidatesS4Dot2 F := by
  intro α p
  exact And.intro
    (axiomT_valid_of_reflexive hRefl p)
    (And.intro
      (axiom4_valid_of_transitive hTrans p)
      (axiomDot2_valid_of_directed hDir p))

theorem validatesGrzDot2Core_of_finite_directed_partialOrder (W : Type u)
    [PartialOrder W] [Finite W]
    (hDir : ∀ w u v,
      (OrderedFrames.orderFrame W).rel w u →
      (OrderedFrames.orderFrame W).rel w v →
      ∃ z, (OrderedFrames.orderFrame W).rel u z ∧ (OrderedFrames.orderFrame W).rel v z) :
    ValidatesGrzDot2Core (OrderedFrames.orderFrame W) := by
  intro α p
  exact And.intro
    (axiomT_valid_of_reflexive (F := OrderedFrames.orderFrame W) (fun _ => le_rfl) p)
    (And.intro
      (axiom4_valid_of_transitive (F := OrderedFrames.orderFrame W)
        (fun _ _ _ => le_trans) p)
      (And.intro
        (axiomDot2_valid_of_directed hDir p)
        (OrderedFrames.axiomGrz_valid_on_finite_partialOrder (W := W) p)))

end HeytingLean.ModalCategorySets.Validities
