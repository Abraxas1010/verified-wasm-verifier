import HeytingLean.Quantum.Translate.Core
import HeytingLean.Quantum.Translate.Omega
import Mathlib.Order.Heyting.Basic

open scoped Classical

namespace HeytingLean.Quantum.Translate

variable {β α : Type _}
variable [HeytingLean.Quantum.OML.OrthocomplementedLattice β]
variable [HeytingLean.Quantum.OML.OrthomodularLattice β]
variable [Order.Frame α]

namespace QLMap

variable (F : QLMap β α)

def toOmega (x : β) : Omega F.M :=
  Omega.mk (M := F.M) (F.M.close (F.tr x)) (by simp)

@[simp] lemma toOmega_coe (x : β) : ((F.toOmega x : Omega F.M) : α) = F.M.close (F.tr x) := rfl

lemma map_inf_toOmega (x y : β) :
  F.toOmega (x ⊓ y) =
    Omega.inf (M := F.M) (F.toOmega x) (F.toOmega y) := by
  -- Coerce both sides and compare in α using closure compatibility with inf.
  ext : 1
  calc
    F.M.close (F.tr (x ⊓ y))
        = F.M.close (F.M.close (F.tr x ⊓ F.tr y)) := by
            simp [F.map_inf]
    _ = F.M.close (F.tr x ⊓ F.tr y) := by
            simp [Modality.close]
    _ = F.M.close (F.tr x) ⊓ F.M.close (F.tr y) := F.M.map_inf _ _

variable [HeytingAlgebra α]

lemma mp (x y : β) :
  Omega.inf (M := F.M) (F.toOmega x)
              (Omega.imp (M := F.M) (F.toOmega x) (F.toOmega y))
  ≤ F.toOmega y := by
  -- Heyting adjunction inside Ω_J.
  have _ := (inferInstance : HeytingAlgebra α)
  change F.toOmega x ⊓ (F.toOmega x ⇨ F.toOmega y) ≤ F.toOmega y
  exact inf_himp_le (a := F.toOmega x) (b := F.toOmega y)

end QLMap

end HeytingLean.Quantum.Translate
