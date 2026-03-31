import HeytingLean.Numbers.SurrealCore
import HeytingLean.Numbers.Surreal.Equiv

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore

/-- Representative-level order: compare canonical forms via the finite-day `le`. -/
noncomputable def leRep (x y : PreGame) : Prop :=
  SurrealCore.le (SurrealCore.canonicalize x) (SurrealCore.canonicalize y)

lemma leRep_respect {x x' y y' : PreGame} :
    approx x x' → approx y y' → (leRep x y ↔ leRep x' y') := by
  intro hxx' hyy'
  unfold leRep approx at *
  simpa [hxx', hyy']

/-- Lifted order on the canonical quotient `SurrealQ`. -/
noncomputable def leQ : SurrealQ → SurrealQ → Prop :=
  Quot.lift₂ leRep
    (by
      intro a a' b b' haa' hbb'
      exact propext (leRep_respect (x:=a) (x':=a') (y:=b) (y':=b') haa' hbb'))

instance : LE SurrealQ where
  le := leQ

@[simp] lemma leQ_mk (x y : PreGame) :
    leQ (Quot.mk approxSetoid x) (Quot.mk approxSetoid y) ↔ leRep x y := Iff.rfl

noncomputable def ltQ (x y : SurrealQ) : Prop :=
  ¬ leQ y x

end Surreal
end Numbers
end HeytingLean

