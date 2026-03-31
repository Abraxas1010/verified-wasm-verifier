import HeytingLean.ModalCategorySets.Propositional.Theories
import HeytingLean.ModalCategorySets.Framework.KripkeCategory

namespace HeytingLean.ModalCategorySets.Propositional

universe u v

namespace Frame

variable {W : Type u} {α : Type v}

/-- Validity at a designated world. -/
def ValidAt (F : Frame W) (w : W) (φ : Formula α) : Prop :=
  ∀ (val : W → α → Prop), satisfies (mkModel F val) w φ

end Frame

/-- Euclidean accessibility restricted to the cone above `w`. -/
def EuclideanAt {W : Type u} (F : Frame W) (w : W) : Prop :=
  ∀ u v, F.rel w u → F.rel w v → F.rel u v

/-- The point `w` only accesses itself. -/
def IsolatedAt {W : Type u} (F : Frame W) (w : W) : Prop :=
  ∀ v, F.rel w v ↔ v = w

end HeytingLean.ModalCategorySets.Propositional

namespace HeytingLean.ModalCategorySets.Validities

open HeytingLean.ModalCategorySets.Propositional
open HeytingLean.ModalCategorySets.Framework

universe u v

theorem valid_validAt {W : Type u} {α : Type v} (F : Frame W) (w : W) (φ : Formula α)
    (hValid : F.Valid φ) :
    F.ValidAt w φ := by
  intro val
  exact hValid val w

theorem axiomK_validAt {W : Type u} {α : Type v} (F : Frame W) (w : W) (p q : α) :
    F.ValidAt w (axiomK p q) :=
  valid_validAt F w _ (axiomK_valid F p q)

theorem axiomT_validAt_of_reflexive {W : Type u} {α : Type v} {F : Frame W}
    (hRefl : Reflexive F) (w : W) (p : α) :
    F.ValidAt w (axiomT p) :=
  valid_validAt F w _ (axiomT_valid_of_reflexive hRefl p)

theorem axiom4_validAt_of_transitive {W : Type u} {α : Type v} {F : Frame W}
    (hTrans : Transitive F) (w : W) (p : α) :
    F.ValidAt w (axiom4 p) :=
  valid_validAt F w _ (axiom4_valid_of_transitive hTrans p)

theorem axiom5_validAt_of_euclideanAt {W : Type u} {α : Type v} {F : Frame W}
    {w : W} (hEucl : EuclideanAt F w) (p : α) :
    F.ValidAt w (axiom5 p) := by
  intro val hDia
  rcases hDia with ⟨u, hwu, hpu⟩
  intro v hwv
  exact Exists.intro u (And.intro (hEucl v u hwv hwu) hpu)

/-- Local S4-validity at a designated world. -/
def ValidatesAtS4 {W : Type u} (F : Frame W) (w : W) : Prop :=
  ∀ {α : Type v} (p : α), F.ValidAt w (axiomT p) ∧ F.ValidAt w (axiom4 p)

/-- Local S5-validity at a designated world. -/
def ValidatesAtS5 {W : Type u} (F : Frame W) (w : W) : Prop :=
  ∀ {α : Type v} (p : α),
    F.ValidAt w (axiomT p) ∧ F.ValidAt w (axiom4 p) ∧ F.ValidAt w (axiom5 p)

theorem validatesAtS4_of_reflexive_transitive {W : Type u} (F : Frame W) (w : W)
    (hRefl : Reflexive F) (hTrans : Transitive F) :
    ValidatesAtS4 F w := by
  intro α p
  exact And.intro (axiomT_validAt_of_reflexive hRefl w p)
    (axiom4_validAt_of_transitive hTrans w p)

theorem validatesAtS5_of_reflexive_transitive_euclideanAt {W : Type u} (F : Frame W) (w : W)
    (hRefl : Reflexive F) (hTrans : Transitive F) (hEucl : EuclideanAt F w) :
    ValidatesAtS5 F w := by
  intro α p
  exact And.intro
    (axiomT_validAt_of_reflexive hRefl w p)
    (And.intro
      (axiom4_validAt_of_transitive hTrans w p)
      (axiom5_validAt_of_euclideanAt hEucl p))

theorem axiomTriv_validAt_of_isolatedAt {W : Type u} {α : Type v} {F : Frame W}
    {w : W} (hIso : IsolatedAt F w) (p : α) :
    F.ValidAt w (axiomTriv p) := by
  intro val
  constructor
  · intro hp v hwv
    have hv : v = w := (hIso v).1 hwv
    cases hv
    simpa [HeytingLean.Logics.Modal.satisfies] using hp
  · intro hBox
    exact hBox w ((hIso w).2 rfl)

theorem euclideanAt_of_coneInvertible {Obj : Type u} (C : KripkeCategory Obj) {w : Obj}
    (hInv : ConeInvertibleAt C w) :
    EuclideanAt C.toFrame w := by
  intro u v hwu hwv
  have huw : C.toFrame.rel u w := hInv u hwu
  exact KripkeCategory.frame_transitive (C := C) u w v huw hwv

theorem validatesAtS5_of_coneInvertible {Obj : Type u} (C : KripkeCategory Obj) (w : Obj)
    (hInv : ConeInvertibleAt C w) :
    ValidatesAtS5 C.toFrame w :=
  validatesAtS5_of_reflexive_transitive_euclideanAt C.toFrame w
    (KripkeCategory.frame_reflexive (C := C))
    (KripkeCategory.frame_transitive (C := C))
    (euclideanAt_of_coneInvertible (C := C) hInv)

end HeytingLean.ModalCategorySets.Validities

namespace HeytingLean.ModalCategorySets.Propositional

open Frame

universe u v

/-- World-level validity wrapper for the currently implemented modal theories. -/
def ModalTheory.ValidatesAt {W : Type u} (F : Frame W) (w : W) : ModalTheory → Prop
  | .K => ∀ {α : Type v} (p q : α), F.ValidAt w (axiomK p q)
  | .S4 => ∀ {α : Type v} (p : α), F.ValidAt w (axiomT p) ∧ F.ValidAt w (axiom4 p)
  | .S5 => ∀ {α : Type v} (p : α),
      F.ValidAt w (axiomT p) ∧ F.ValidAt w (axiom4 p) ∧ F.ValidAt w (axiom5 p)
  | .Triv => ∀ {α : Type v} (p : α), F.ValidAt w (axiomTriv p)

end HeytingLean.ModalCategorySets.Propositional
