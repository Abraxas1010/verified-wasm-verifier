import HeytingLean.InqBQ.FragmentHardness

namespace HeytingLean.Tests.InqBQ

open HeytingLean.InqBQ

example :
    h10upcToFiniteValidityBridge.targetPred = finiteValidityFamily := rfl

example :
    h10upcToInqbqValidityBridge.targetPred = inqbqValidityFamily := rfl

example :
    ¬ REPred finiteValidityFamily :=
  finite_validity_family_not_re

example :
    ¬ REPred inqbqValidityFamily :=
  inqbq_validity_family_not_re_via_transport

end HeytingLean.Tests.InqBQ
