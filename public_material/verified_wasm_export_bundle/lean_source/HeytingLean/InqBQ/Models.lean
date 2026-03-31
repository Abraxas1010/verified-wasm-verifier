import HeytingLean.InqBQ.Syntax

namespace HeytingLean
namespace InqBQ

open Classical

variable {sig : Signature}

/-- A first-order information model for InqBQ. -/
structure InfoModel (sig : Signature) where
  W : Type
  D : Type
  hW : Nonempty W
  hD : Nonempty D
  predInterp :
    (w : W) → (P : sig.PredSym) → (Fin (sig.predArity P) → D) → Prop
  rigidInterp :
    (f : sig.RigidFun) → (Fin (sig.rigidArity f) → D) → D
  nonrigidInterp :
    (w : W) → (f : sig.NonRigidFun) → (Fin (sig.nonrigidArity f) → D) → D
  localEq : W → D → D → Prop
  localEq_equiv : ∀ w, Equivalence (localEq w)
  localEq_congr_pred :
    ∀ {w : W} {P : sig.PredSym} {xs ys : Fin (sig.predArity P) → D},
      (∀ i, localEq w (xs i) (ys i)) →
        (predInterp w P xs ↔ predInterp w P ys)
  localEq_congr_rigid :
    ∀ {w : W} {f : sig.RigidFun} {xs ys : Fin (sig.rigidArity f) → D},
      (∀ i, localEq w (xs i) (ys i)) →
        localEq w (rigidInterp f xs) (rigidInterp f ys)
  localEq_congr_nonrigid :
    ∀ {w : W} {f : sig.NonRigidFun} {xs ys : Fin (sig.nonrigidArity f) → D},
      (∀ i, localEq w (xs i) (ys i)) →
        localEq w (nonrigidInterp w f xs) (nonrigidInterp w f ys)

namespace InfoModel

/-- An id-model is an information model where local equality is ordinary equality. -/
def isIdModel (M : InfoModel sig) : Prop :=
  ∀ w d d', M.localEq w d d' ↔ d = d'

end InfoModel

/-- Assignments map free variables to domain elements. -/
abbrev Assignment (D : Type) := ℕ → D

namespace Assignment

/-- Update one variable in an assignment. -/
def update (g : Assignment D) (x : ℕ) (d : D) : Assignment D :=
  fun y => if y = x then d else g y

@[simp] theorem update_same (g : Assignment D) (x : ℕ) (d : D) :
    update g x d x = d := by
  simp [update]

@[simp] theorem update_ne (g : Assignment D) {x y : ℕ} (d : D) (h : y ≠ x) :
    update g x d y = g y := by
  simp [update, h]

end Assignment

/-- Denotation of a term at a world under an assignment. -/
def denote (M : InfoModel sig) (w : M.W) (g : Assignment M.D) : Term sig → M.D
  | .var x => g x
  | .rigidApp f args => M.rigidInterp f (fun i => denote M w g (args i))
  | .nonrigidApp f args => M.nonrigidInterp w f (fun i => denote M w g (args i))

end InqBQ
end HeytingLean
