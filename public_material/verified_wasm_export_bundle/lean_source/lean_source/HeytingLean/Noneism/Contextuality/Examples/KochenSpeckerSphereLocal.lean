import HeytingLean.Noneism.Contextuality.GlobalSection
import HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerDeep.Basic

namespace HeytingLean
namespace Noneism
namespace Contextuality
namespace Examples
namespace KochenSpeckerSphereLocal

open KochenSpeckerDeep

/--
Finite local observables for a compact KS-style parity scenario.
The constraints are fully local (context-wise) and do not quantify over
global assignments.
-/
inductive Obs where
  | ox
  | oy
  | oz
deriving DecidableEq, Fintype

abbrev Outcome := SpinMeasurement
abbrev Ctx := Context Obs

def cxy : Ctx := ({Obs.ox, Obs.oy} : Finset Obs)
def cyz : Ctx := ({Obs.oy, Obs.oz} : Finset Obs)
def cxz : Ctx := ({Obs.ox, Obs.oz} : Finset Obs)

def ksCover : Finset Ctx := {cxy, cyz, cxz}

lemma cxy_mem_cover : cxy ∈ ksCover := by simp [ksCover]
lemma cyz_mem_cover : cyz ∈ ksCover := by simp [ksCover]
lemma cxz_mem_cover : cxz ∈ ksCover := by simp [ksCover]

lemma cxy_ne_cyz : cxy ≠ cyz := by decide
lemma cxy_ne_cxz : cxy ≠ cxz := by decide
lemma cyz_ne_cxy : cyz ≠ cxy := by decide
lemma cyz_ne_cxz : cyz ≠ cxz := by decide
lemma cxz_ne_cxy : cxz ≠ cxy := by decide
lemma cxz_ne_cyz : cxz ≠ cyz := by decide

def xorAllowed (a b : Outcome) : Prop :=
  (a = SpinMeasurement.zero ∧ b = SpinMeasurement.one) ∨
  (a = SpinMeasurement.one ∧ b = SpinMeasurement.zero)

def allowed (C : Ctx) (s : LocalAssign C Outcome) : Prop :=
  if hxy : C = cxy then
    xorAllowed
      (s ⟨Obs.ox, by simp [hxy, cxy]⟩)
      (s ⟨Obs.oy, by simp [hxy, cxy]⟩)
  else if hyz : C = cyz then
    xorAllowed
      (s ⟨Obs.oy, by simp [hyz, cyz]⟩)
      (s ⟨Obs.oz, by simp [hyz, cyz]⟩)
  else if hxz : C = cxz then
    xorAllowed
      (s ⟨Obs.ox, by simp [hxz, cxz]⟩)
      (s ⟨Obs.oz, by simp [hxz, cxz]⟩)
  else
    False

def ksScenarioLocal : Scenario Obs Outcome where
  cover := ksCover
  covers_all := by
    intro o
    cases o with
    | ox =>
        exact ⟨cxy, cxy_mem_cover, by simp [cxy]⟩
    | oy =>
        exact ⟨cxy, cxy_mem_cover, by simp [cxy]⟩
    | oz =>
        exact ⟨cyz, cyz_mem_cover, by simp [cyz]⟩
  Allowed := allowed

lemma global_implies_xy_xor {g : Obs → Outcome}
    (hGlobal : IsGlobalSection ksScenarioLocal g) :
    xorAllowed (g Obs.ox) (g Obs.oy) := by
  have hAllowed := hGlobal cxy cxy_mem_cover
  simpa [ksScenarioLocal, allowed, cxy, cyz, cxz, cxy_ne_cyz, cxy_ne_cxz, xorAllowed, restrict]
    using hAllowed

lemma global_implies_yz_xor {g : Obs → Outcome}
    (hGlobal : IsGlobalSection ksScenarioLocal g) :
    xorAllowed (g Obs.oy) (g Obs.oz) := by
  have hAllowed := hGlobal cyz cyz_mem_cover
  simpa [ksScenarioLocal, allowed, cxy, cyz, cxz, cyz_ne_cxy, cyz_ne_cxz, xorAllowed, restrict]
    using hAllowed

lemma global_implies_xz_xor {g : Obs → Outcome}
    (hGlobal : IsGlobalSection ksScenarioLocal g) :
    xorAllowed (g Obs.ox) (g Obs.oz) := by
  have hAllowed := hGlobal cxz cxz_mem_cover
  simpa [ksScenarioLocal, allowed, cxy, cyz, cxz, cxz_ne_cxy, cxz_ne_cyz, xorAllowed, restrict]
    using hAllowed

lemma xorAllowed_iff_ne (a b : Outcome) : xorAllowed a b ↔ a ≠ b := by
  cases a <;> cases b <;> simp [xorAllowed]

lemma no_three_pairwise_ne (a b c : Outcome) :
    ¬ (a ≠ b ∧ b ≠ c ∧ a ≠ c) := by
  cases a <;> cases b <;> cases c <;> simp

abbrev OneZeroOneLocal := {g : Obs → Outcome // IsGlobalSection ksScenarioLocal g}

theorem globalSection_to_oneZeroOne_local :
    (∃ g : Obs → Outcome, IsGlobalSection ksScenarioLocal g) → Nonempty OneZeroOneLocal := by
  intro h
  rcases h with ⟨g, hg⟩
  exact ⟨⟨g, hg⟩⟩

theorem oneZeroOne_to_globalSection_local :
    Nonempty OneZeroOneLocal → ∃ g : Obs → Outcome, IsGlobalSection ksScenarioLocal g := by
  intro h
  rcases h with ⟨⟨g, hg⟩⟩
  exact ⟨g, hg⟩

theorem ksScenarioLocal_no_global_section :
    ¬ ∃ g : Obs → Outcome, IsGlobalSection ksScenarioLocal g := by
  intro h
  rcases h with ⟨g, hg⟩
  have hxy : g Obs.ox ≠ g Obs.oy :=
    (xorAllowed_iff_ne _ _).1 (global_implies_xy_xor hg)
  have hyz : g Obs.oy ≠ g Obs.oz :=
    (xorAllowed_iff_ne _ _).1 (global_implies_yz_xor hg)
  have hxz : g Obs.ox ≠ g Obs.oz :=
    (xorAllowed_iff_ne _ _).1 (global_implies_xz_xor hg)
  exact (no_three_pairwise_ne (g Obs.ox) (g Obs.oy) (g Obs.oz)) ⟨hxy, hyz, hxz⟩

theorem ksScenarioLocal_contextual : Contextual ksScenarioLocal :=
  ksScenarioLocal_no_global_section

end KochenSpeckerSphereLocal
end Examples
end Contextuality
end Noneism
end HeytingLean
