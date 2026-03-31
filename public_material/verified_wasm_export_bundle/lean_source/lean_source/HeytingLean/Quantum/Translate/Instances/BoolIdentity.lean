import HeytingLean.Quantum.OML.Sasaki
import HeytingLean.Quantum.Translate.Modality
import HeytingLean.Quantum.Translate.Core

open scoped Classical

namespace HeytingLean.Quantum.Translate.Instances

open HeytingLean.Quantum.OML

/-- Identity modality on a complete lattice, re-exposed for Boolean examples. -/
def boolIdModality (α : Type _) [CompleteLattice α] : Modality α := Modality.id α

/-- Identity translation on a complete Boolean algebra, landing in the same carrier. -/
def boolIdentityQLMap (α : Type _) [CompleteBooleanAlgebra α] : QLMap α α :=
{ M := boolIdModality α
  tr := id
  map_inf := by intro x y; rfl
  map_sup_le := by intro _ _; exact le_rfl }

@[simp] instance boolIdentityComplPreserving (α : Type _) [CompleteBooleanAlgebra α] :
    QLMap.ComplPreserving (F := boolIdentityQLMap α) :=
by
  refine ⟨?_⟩
  intro a
  rfl

end HeytingLean.Quantum.Translate.Instances
