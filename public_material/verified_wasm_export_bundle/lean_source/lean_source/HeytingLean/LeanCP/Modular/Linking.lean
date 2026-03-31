import HeytingLean.LeanCP.Modular.Compose

/-!
# LeanCP VSU Linking

The Phase 9 link checker is intentionally fail-closed on duplicate export names.
Peer imports are resolved compositionally and any remaining external imports stay
visible on the linked unit.
-/

namespace HeytingLean.LeanCP.Modular

open Classical

def linkable (u1 u2 : VSU) : Prop :=
  NamesDisjoint u1.exportNames u2.exportNames

instance (u1 u2 : VSU) : Decidable (linkable u1 u2) := by
  classical
  unfold linkable
  infer_instance

def link (u1 u2 : VSU) : Option VSU :=
  if hlink : linkable u1 u2 then
    some (compose u1 u2 hlink)
  else
    none

theorem link_eq_some {u1 u2 : VSU} {hlink : linkable u1 u2} :
    link u1 u2 = some (compose u1 u2 hlink) := by
  unfold link
  simp [hlink]

theorem link_sound {u1 u2 u : VSU}
    (hlink : link u1 u2 = some u) :
    ∀ proc, proc ∈ u.exports →
      LoopFree proc.spec.body ∧
      TailReturn proc.spec.body ∧
      MustReturn proc.spec.body ∧
      sgenVCFull proc.verifyEnv proc.spec := by
  unfold link at hlink
  by_cases h : linkable u1 u2
  · simp [h] at hlink
    cases hlink
    simpa using compose_sound u1 u2 h
  · simp [h] at hlink

theorem link_left_export_sound {u1 u2 u : VSU}
    (hlink : link u1 u2 = some u) {proc : VerifiedProc}
    (hmem : proc ∈ u1.exports) :
    VSU.exportSound u proc.spec.name := by
  unfold link at hlink
  by_cases h : linkable u1 u2
  · simp [h] at hlink
    cases hlink
    simpa using compose_left_export_sound u1 u2 h hmem
  · simp [h] at hlink

theorem link_right_export_sound {u1 u2 u : VSU}
    (hlink : link u1 u2 = some u) {proc : VerifiedProc}
    (hmem : proc ∈ u2.exports) :
    VSU.exportSound u proc.spec.name := by
  unfold link at hlink
  by_cases h : linkable u1 u2
  · simp [h] at hlink
    cases hlink
    simpa using compose_right_export_sound u1 u2 h hmem
  · simp [h] at hlink

theorem link_resolves_left_import {u1 u2 u : VSU} (hlink : link u1 u2 = some u)
    {name : String} (himp : name ∈ u1.imports) (hprov : name ∈ u2.exportNames)
    (habsent : name ∉ u2.imports) :
    name ∉ u.imports := by
  unfold link at hlink
  by_cases h : linkable u1 u2
  · simp [h] at hlink
    cases hlink
    simpa [compose] using
      resolved_left_import_not_remaining (u1 := u1) (u2 := u2) himp hprov habsent
  · simp [h] at hlink

theorem link_resolves_right_import {u1 u2 u : VSU} (hlink : link u1 u2 = some u)
    {name : String} (himp : name ∈ u2.imports) (hprov : name ∈ u1.exportNames)
    (habsent : name ∉ u1.imports) :
    name ∉ u.imports := by
  unfold link at hlink
  by_cases h : linkable u1 u2
  · simp [h] at hlink
    cases hlink
    simpa [compose] using
      resolved_right_import_not_remaining (u1 := u1) (u2 := u2) himp hprov habsent
  · simp [h] at hlink

end HeytingLean.LeanCP.Modular
