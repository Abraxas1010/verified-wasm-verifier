import HeytingLean.InqBQ.FragmentHardness

namespace HeytingLean
namespace InqBQ

/--
Final non-r.e. endpoint on the translated InqBQ validity family.

This is the closure target for the H10UPC → finite-validity → InqBQ reduction lane:
the family of InqBQ validities obtained from the imported finite-validity bridge is
not recursively enumerable.
-/
theorem inqbq_validity_family_not_re :
    ¬ REPred
      (fun cs : List H10UPC =>
        idValid (sig := ABSignature ReductionSig) (reductionValidityFormula cs)) := by
  simpa [inqbqValidityFamily] using inqbq_validity_family_not_re_via_transport

end InqBQ
end HeytingLean
