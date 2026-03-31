import HeytingLean.InqBQ.Imported.H10UPCFiniteValidityCorrectness

namespace HeytingLean
namespace InqBQ

/-- Classical finite-validity family on the fixed binary signature. -/
def finiteValidityFamily (cs : List H10UPC) : Prop :=
  finiteFOLValid (h10upcFiniteValidityFormula cs)

theorem finiteValidityFamily_correct (cs : List H10UPC) :
    finiteValidityFamily cs ↔ ¬ H10UPCSat cs :=
  Imported.h10upcFiniteValidityFormula_correct cs

/-- The corresponding InqBQ validity instance produced by `finite_validity_reduction`. -/
noncomputable def reductionValidityFormula (cs : List H10UPC) : Formula (ABSignature ReductionSig) :=
  .imp etaAB
    (.inqDisj (ABSignature.embedFormula (h10upcFiniteValidityFormula cs)) thetaAB)

/-- The InqBQ validity family induced by the native finite-validity formula family. -/
def inqbqValidityFamily (cs : List H10UPC) : Prop :=
  idValid (sig := ABSignature ReductionSig) (reductionValidityFormula cs)

theorem reductionValidityFormula_correct (cs : List H10UPC) :
    inqbqValidityFamily cs ↔ ¬ H10UPCSat cs := by
  have hFin :
      finiteFOLValid (h10upcFiniteValidityFormula cs) ↔
        inqbqValidityFamily cs :=
    finite_validity_reduction
      (sig := ReductionSig)
      (α := h10upcFiniteValidityFormula cs)
      (h10upcFiniteValidityFormula_classical cs)
  exact hFin.symm.trans (Imported.h10upcFiniteValidityFormula_correct cs)

end InqBQ
end HeytingLean
