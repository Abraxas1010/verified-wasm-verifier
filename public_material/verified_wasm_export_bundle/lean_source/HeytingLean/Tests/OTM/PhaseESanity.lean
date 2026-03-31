import HeytingLean.OTM.PerspectivalHalting

namespace HeytingLean.Tests.OTM

open HeytingLean.OTM

example :
    ¬ profileHaltsBy dim2Profile counterTM 0 :=
  dim2Profile_no_halt_for_counterTM

example :
    profileHaltsBy dim3Profile counterTM 0 :=
  dim3Profile_halts_for_counterTM

example :
    ¬ profileHaltsBy dim2Profile counterTM 0 ∧
      profileHaltsBy dim3Profile counterTM 0 :=
  otm_perspectival_halting_witness

example :
    ∃ P₂ P₃ : PerspectivalPlenum.Lens.LensProfile,
      P₂.dimension = 2 ∧ P₃.dimension = 3 ∧
      ¬ profileHaltsBy P₂ counterTM 0 ∧ profileHaltsBy P₃ counterTM 0 :=
  halting_is_perspectival

end HeytingLean.Tests.OTM
