import HeytingLean.ModalCategorySets.Propositional.Axioms
import HeytingLean.ModalCategorySets.Framework.KripkeCategory

namespace HeytingLean.ModalCategorySets.Validities

open HeytingLean.ModalCategorySets.Propositional
open HeytingLean.ModalCategorySets.Framework

universe u v

theorem axiomK_valid {W : Type u} (F : Frame W) {α : Type v} (p q : α) :
    F.Valid (axiomK p q) := by
  intro val w hImpBox hBoxP v hwv
  exact hImpBox v hwv (hBoxP v hwv)

theorem axiomT_valid_of_reflexive {W : Type u} {α : Type v} {F : Frame W}
    (hRefl : Reflexive F) (p : α) :
    F.Valid (axiomT p) := by
  intro val w hBox
  exact hBox w (hRefl w)

theorem axiom4_valid_of_transitive {W : Type u} {α : Type v} {F : Frame W}
    (hTrans : Transitive F) (p : α) :
    F.Valid (axiom4 p) := by
  intro val w hBox v hwv u hvu
  exact hBox u (hTrans w v u hwv hvu)

theorem axiom5_valid_of_euclidean {W : Type u} {α : Type v} {F : Frame W}
    (hEucl : Euclidean F) (p : α) :
    F.Valid (axiom5 p) := by
  intro val w hDia v hwv
  rcases hDia with ⟨u, hwu, hpu⟩
  exact Exists.intro u (And.intro (hEucl w v u hwv hwu) hpu)

/-- S4-validity at the frame level: every variable instance validates both T and 4. -/
def ValidatesS4 {W : Type u} (F : Frame W) : Prop :=
  ∀ {α : Type v} (p : α), F.Valid (axiomT p) ∧ F.Valid (axiom4 p)

/-- S5-validity at the frame level: every variable instance validates T, 4, and 5. -/
def ValidatesS5 {W : Type u} (F : Frame W) : Prop :=
  ∀ {α : Type v} (p : α), F.Valid (axiomT p) ∧ F.Valid (axiom4 p) ∧ F.Valid (axiom5 p)

theorem validatesS4_of_reflexive_transitive {W : Type u} (F : Frame W)
    (hRefl : Reflexive F) (hTrans : Transitive F) :
    ValidatesS4 F := by
  intro α p
  exact And.intro (axiomT_valid_of_reflexive hRefl p) (axiom4_valid_of_transitive hTrans p)

theorem validatesS5_of_reflexive_transitive_euclidean {W : Type u} (F : Frame W)
    (hRefl : Reflexive F) (hTrans : Transitive F) (hEucl : Euclidean F) :
    ValidatesS5 F := by
  intro α p
  exact And.intro
    (axiomT_valid_of_reflexive hRefl p)
    (And.intro (axiom4_valid_of_transitive hTrans p) (axiom5_valid_of_euclidean hEucl p))

theorem s4_valid_in_kripke_category {Obj : Type u} (C : KripkeCategory Obj) :
    ValidatesS4 C.toFrame :=
  validatesS4_of_reflexive_transitive C.toFrame C.frame_reflexive C.frame_transitive

theorem axiomTriv_valid_of_identityRelation {W : Type u} {α : Type v} {F : Frame W}
    (hId : IsIdentityRelation F) (p : α) :
    F.Valid (axiomTriv p) := by
  intro val w
  constructor
  · intro hp v hv
    have hwv : w = v := (hId w v).1 hv
    cases hwv
    simpa [HeytingLean.Logics.Modal.satisfies] using hp
  · intro hBox
    exact hBox w ((hId w w).2 rfl)

theorem axiomTriv_valid_on_identityFrame {α : Type v} (p : α) :
    identityFrame.Valid (axiomTriv p) :=
  axiomTriv_valid_of_identityRelation identityFrame_isIdentityRelation p

open scoped Classical

noncomputable def inverseOfBijective {α β : Type u}
    (f : α → β) (hf : Function.Bijective f) : β → α :=
  fun b => Classical.choose (hf.surjective b)

theorem inverseOfBijective_rightInverse {α β : Type u}
    (f : α → β) (hf : Function.Bijective f) :
    Function.RightInverse (inverseOfBijective f hf) f := by
  intro b
  exact Classical.choose_spec (hf.surjective b)

theorem inverseOfBijective_leftInverse {α β : Type u}
    (f : α → β) (hf : Function.Bijective f) :
    Function.LeftInverse (inverseOfBijective f hf) f := by
  intro a
  apply hf.injective
  exact Classical.choose_spec (hf.surjective (f a))

theorem inverseOfBijective_bijective {α β : Type u}
    (f : α → β) (hf : Function.Bijective f) :
    Function.Bijective (inverseOfBijective f hf) := by
  constructor
  · intro b₁ b₂ hEq
    have hApply : f (inverseOfBijective f hf b₁) = f (inverseOfBijective f hf b₂) :=
      congrArg f hEq
    calc
      b₁ = f (inverseOfBijective f hf b₁) := by
        symm
        exact inverseOfBijective_rightInverse f hf b₁
      _ = f (inverseOfBijective f hf b₂) := hApply
      _ = b₂ := inverseOfBijective_rightInverse f hf b₂
  · intro a
    exact Exists.intro (f a) (inverseOfBijective_leftInverse f hf a)

theorem bijections_frame_symmetric :
    Symmetric (bijections.toKripkeCategory.toFrame) := by
  intro α β h
  rcases h with ⟨f⟩
  exact Nonempty.intro (Subtype.mk
    (inverseOfBijective f.1 f.2)
    (inverseOfBijective_bijective f.1 f.2))

theorem bijections_frame_euclidean :
    Euclidean (bijections.toKripkeCategory.toFrame) := by
  intro α β γ hαβ hαγ
  have hβα : (bijections.toKripkeCategory.toFrame).rel β α :=
    bijections_frame_symmetric α β hαβ
  exact KripkeCategory.frame_transitive (C := bijections.toKripkeCategory) β α γ hβα hαγ

theorem s5_valid_on_bijections :
    ValidatesS5 (bijections.toKripkeCategory.toFrame) :=
  validatesS5_of_reflexive_transitive_euclidean
    (bijections.toKripkeCategory.toFrame)
    (KripkeCategory.frame_reflexive (C := bijections.toKripkeCategory))
    (KripkeCategory.frame_transitive (C := bijections.toKripkeCategory))
    bijections_frame_euclidean

theorem triv_valid_on_identityCategory {α : Type v} (p : α) :
    identityCategory.toFrame.Valid (axiomTriv p) := by
  exact axiomTriv_valid_of_identityRelation identityCategory_frame_isIdentityRelation p

end HeytingLean.ModalCategorySets.Validities
