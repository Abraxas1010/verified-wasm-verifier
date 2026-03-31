import HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerSphereLocal
import HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerDeep.KochenSpecker

namespace HeytingLean
namespace Noneism
namespace Contextuality
namespace Examples
namespace KochenSpeckerSphere

open KochenSpeckerDeep

abbrev OneZeroOneFunc := KochenSpeckerDeep.OneZeroOneFunc

theorem no_one_zero_one : OneZeroOneFunc → False :=
  KochenSpeckerDeep.kochen_specker

theorem no_noncontextual_global_assignment : ¬ Nonempty OneZeroOneFunc := by
  intro h
  exact no_one_zero_one h.some

abbrev Obs := KochenSpeckerSphereLocal.Obs
abbrev Outcome := KochenSpeckerSphereLocal.Outcome
abbrev Ctx := KochenSpeckerSphereLocal.Ctx
abbrev ksScenario : Scenario Obs Outcome := KochenSpeckerSphereLocal.ksScenarioLocal
abbrev OneZeroOneLocal := KochenSpeckerSphereLocal.OneZeroOneLocal

theorem globalSection_to_oneZeroOne_local :
    (∃ g : Obs → Outcome, IsGlobalSection ksScenario g) → Nonempty OneZeroOneLocal :=
  KochenSpeckerSphereLocal.globalSection_to_oneZeroOne_local

theorem oneZeroOne_to_globalSection_local :
    Nonempty OneZeroOneLocal → ∃ g : Obs → Outcome, IsGlobalSection ksScenario g :=
  KochenSpeckerSphereLocal.oneZeroOne_to_globalSection_local

theorem oneZeroOne_of_global_section :
    (∃ g : Obs → Outcome, IsGlobalSection ksScenario g) → Nonempty OneZeroOneLocal :=
  globalSection_to_oneZeroOne_local

theorem global_section_of_oneZeroOne (h : Nonempty OneZeroOneLocal) :
    ∃ g : Obs → Outcome, IsGlobalSection ksScenario g :=
  oneZeroOne_to_globalSection_local h

theorem ksScenario_no_global_section :
    ¬ ∃ g : Obs → Outcome, IsGlobalSection ksScenario g :=
  KochenSpeckerSphereLocal.ksScenarioLocal_no_global_section

theorem ksScenario_contextual : Contextual ksScenario :=
  KochenSpeckerSphereLocal.ksScenarioLocal_contextual

end KochenSpeckerSphere
end Examples
end Contextuality
end Noneism
end HeytingLean
