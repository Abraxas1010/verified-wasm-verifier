import Mathlib.Data.List.Basic
import HeytingLean.LeanCP.Modular.VSU

/-!
# LeanCP Modular Composition

Composition preserves already-proved exported contracts and resolves peer import
names without re-running the verifier.
-/

namespace HeytingLean.LeanCP.Modular

open Classical
open HeytingLean.LeanCP

/-- Imports that remain after internal name-level resolution between two units. -/
def remainingImports (u1 u2 : VSU) : List String :=
  (u1.imports.filter (fun name => name ∉ u2.exportNames)) ++
    (u2.imports.filter (fun name => name ∉ u1.exportNames))

theorem mem_remainingImports {u1 u2 : VSU} {name : String} :
    name ∈ remainingImports u1 u2 ↔
      (name ∈ u1.imports ∧ name ∉ u2.exportNames) ∨
      (name ∈ u2.imports ∧ name ∉ u1.exportNames) := by
  classical
  simp [remainingImports]

theorem resolved_left_import_not_remaining {u1 u2 : VSU} {name : String}
    (himp : name ∈ u1.imports) (hprov : name ∈ u2.exportNames) (habsent : name ∉ u2.imports) :
    name ∉ remainingImports u1 u2 := by
  intro hrem
  rcases (mem_remainingImports.mp hrem) with hleft | hright
  · exact hleft.2 hprov
  · exact habsent hright.1

theorem resolved_right_import_not_remaining {u1 u2 : VSU} {name : String}
    (himp : name ∈ u2.imports) (hprov : name ∈ u1.exportNames) (habsent : name ∉ u1.imports) :
    name ∉ remainingImports u1 u2 := by
  intro hrem
  rcases (mem_remainingImports.mp hrem) with hleft | hright
  · exact habsent hleft.1
  · exact hright.2 hprov

theorem procNames_append_nodup {xs ys : List VerifiedProc}
    (hxs : (procNames xs).Nodup) (hys : (procNames ys).Nodup)
    (hdisj : NamesDisjoint (procNames xs) (procNames ys)) :
    (procNames (xs ++ ys)).Nodup := by
  classical
  simp [procNames, List.map_append]
  refine (List.nodup_append.mpr ?_)
  refine ⟨hxs, hys, ?_⟩
  intro a ha b hb hab
  exact hdisj a ha (hab ▸ hb)

/-- Binary VSU composition, assuming disjoint export names. -/
def compose (u1 u2 : VSU) (hdisj : NamesDisjoint u1.exportNames u2.exportNames) : VSU where
  name := s!"{u1.name}+{u2.name}"
  imports := remainingImports u1 u2
  exports := u1.exports ++ u2.exports
  exports_nodup := procNames_append_nodup u1.exports_nodup u2.exports_nodup hdisj

/-- Every exported contract survives composition unchanged. -/
theorem compose_sound (u1 u2 : VSU) (hdisj : NamesDisjoint u1.exportNames u2.exportNames) :
    ∀ proc, proc ∈ (compose u1 u2 hdisj).exports →
      LoopFree proc.spec.body ∧
      TailReturn proc.spec.body ∧
      MustReturn proc.spec.body ∧
      sgenVCFull proc.verifyEnv proc.spec := by
  intro proc hmem
  simp [compose] at hmem
  rcases hmem with hleft | hright
  · exact proc.sound
  · exact proc.sound

theorem compose_left_export_sound (u1 u2 : VSU)
    (hdisj : NamesDisjoint u1.exportNames u2.exportNames)
    {proc : VerifiedProc} (hmem : proc ∈ u1.exports) :
    VSU.exportSound (compose u1 u2 hdisj) proc.spec.name := by
  refine ⟨proc, ?_, proc.sound⟩
  exact findProcByName_of_mem (compose u1 u2 hdisj).exports_nodup (by simp [compose, hmem])

theorem compose_right_export_sound (u1 u2 : VSU)
    (hdisj : NamesDisjoint u1.exportNames u2.exportNames)
    {proc : VerifiedProc} (hmem : proc ∈ u2.exports) :
    VSU.exportSound (compose u1 u2 hdisj) proc.spec.name := by
  refine ⟨proc, ?_, proc.sound⟩
  exact findProcByName_of_mem (compose u1 u2 hdisj).exports_nodup (by simp [compose, hmem])

end HeytingLean.LeanCP.Modular
