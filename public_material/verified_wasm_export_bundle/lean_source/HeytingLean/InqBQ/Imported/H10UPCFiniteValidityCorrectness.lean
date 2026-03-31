import HeytingLean.InqBQ.NativeFiniteValidityCorrectness

namespace HeytingLean
namespace InqBQ
namespace Imported

/--
Compatibility wrapper for the now-native H10UPC -> finite-validity correctness
surface.
-/
theorem h10upcFiniteValidityFormula_complete :
    ∀ cs, ¬ H10UPCSat cs → finiteFOLValid (h10upcFiniteValidityFormula cs)
  | cs => HeytingLean.InqBQ.h10upcFiniteValidityFormula_complete cs

theorem h10upcFiniteValidityFormula_correct :
    ∀ cs, finiteFOLValid (h10upcFiniteValidityFormula cs) ↔ ¬ H10UPCSat cs
  | cs => by
      constructor
      · exact h10upcFiniteValidityFormula_correct_forward cs
      · exact h10upcFiniteValidityFormula_complete cs

end Imported
end InqBQ
end HeytingLean
