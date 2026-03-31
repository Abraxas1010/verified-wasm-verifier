import HeytingLean.Quantum.Translate.Modality

/-!
# Darwin's Cage modality layer

This module provides stable, Darwin's Cage names for the identity modality/nucleus
coming from `HeytingLean.Quantum.Translate.Modality`.
-/

namespace HeytingLean
namespace DarwinsCage

namespace Quantum

open scoped Classical

abbrev Modality (α : Type _) [CompleteLattice α] :=
  HeytingLean.Quantum.Translate.Modality α

namespace Modality

variable (α : Type _) [CompleteLattice α]

abbrev id : Quantum.Modality α :=
  HeytingLean.Quantum.Translate.Modality.id α

abbrev idNucleus : Nucleus α :=
  (Modality.id α).J

@[simp] theorem idNucleus_apply (a : α) : Modality.idNucleus α a = a := rfl

end Modality

end Quantum

end DarwinsCage
end HeytingLean

