import Mathlib.Data.List.Basic
import HeytingLean.LeanCP.VCG.SWPCallSound

/-!
# LeanCP Modular Verification Core

Phase 9 packages already-verified LeanCP procedures into first-class verified
software units (VSUs). The key design choice on the current LeanCP surface is
to store exported procedures together with the exact verification environment
they were proved against. Linking then becomes a compositional interface
operation over verified exports and import names, rather than a second verifier.
-/

namespace HeytingLean.LeanCP.Modular

open Classical
open HeytingLean.LeanCP

/-- A loop-free call-aware procedure contract already discharged in LeanCP. -/
structure VerifiedProc where
  spec : SFunSpec
  verifyEnv : FunEnv
  sound :
    LoopFree spec.body ∧
    TailReturn spec.body ∧
    MustReturn spec.body ∧
    sgenVCFull verifyEnv spec

/-- Export-name projection for verified procedures. -/
def procNames (procs : List VerifiedProc) : List String :=
  procs.map (fun proc => proc.spec.name)

/-- Find a verified procedure by its exported name. -/
def findProcByName : List VerifiedProc → String → Option VerifiedProc
  | [], _ => none
  | proc :: procs, name =>
      if proc.spec.name = name then some proc else findProcByName procs name

/-- The string-level disjointness relation used by the Phase 9 link checker. -/
def NamesDisjoint (xs ys : List String) : Prop :=
  ∀ name, name ∈ xs → name ∈ ys → False

instance (xs ys : List String) : Decidable (NamesDisjoint xs ys) := by
  classical
  unfold NamesDisjoint
  infer_instance

theorem NamesDisjoint.symm {xs ys : List String} :
    NamesDisjoint xs ys → NamesDisjoint ys xs := by
  intro h name hy hx
  exact h name hx hy

theorem findProcByName_eq_some_mem {procs : List VerifiedProc} {name : String}
    {proc : VerifiedProc} :
    findProcByName procs name = some proc → proc ∈ procs := by
  induction procs with
  | nil =>
      simp [findProcByName]
  | cons head tail ih =>
      simp [findProcByName]
      by_cases hname : head.spec.name = name
      · intro hlookup
        simp [hname] at hlookup
        cases hlookup
        simp
      · intro hlookup
        simp [hname] at hlookup
        exact Or.inr (ih hlookup)

theorem findProcByName_eq_some_name {procs : List VerifiedProc} {name : String}
    {proc : VerifiedProc} :
    findProcByName procs name = some proc → proc.spec.name = name := by
  induction procs with
  | nil =>
      simp [findProcByName]
  | cons head tail ih =>
      simp [findProcByName]
      by_cases hname : head.spec.name = name
      · intro hlookup
        simp [hname] at hlookup
        cases hlookup
        exact hname
      · intro hlookup
        simp [hname] at hlookup
        exact ih hlookup

theorem findProcByName_of_mem {procs : List VerifiedProc} {proc : VerifiedProc}
    (hnodup : (procNames procs).Nodup) (hmem : proc ∈ procs) :
    findProcByName procs proc.spec.name = some proc := by
  induction procs generalizing proc with
  | nil =>
      cases hmem
  | cons head tail ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hhead, htail⟩
      simp at hmem
      rcases hmem with hEq | htailMem
      · cases hEq
        simp [findProcByName]
      ·
          have hneq : head.spec.name ≠ proc.spec.name := by
            intro heq
            apply hhead
            exact List.mem_map.mpr ⟨proc, htailMem, by simpa [heq] using rfl⟩
          simpa [findProcByName, hneq] using ih htail htailMem

/-- A Phase 9 verified software unit: import names plus independently verified
exported procedures. -/
structure VSU where
  name : String
  imports : List String := []
  exports : List VerifiedProc
  exports_nodup : (procNames exports).Nodup

namespace VSU

def exportNames (u : VSU) : List String :=
  procNames u.exports

def importsResolvedBy (provider consumer : VSU) : Prop :=
  ∀ name, name ∈ consumer.imports → name ∈ provider.exportNames

instance (provider consumer : VSU) : Decidable (provider.importsResolvedBy consumer) := by
  classical
  unfold importsResolvedBy
  infer_instance

def exportSound (u : VSU) (name : String) : Prop :=
  ∃ proc, findProcByName u.exports name = some proc ∧
    LoopFree proc.spec.body ∧
    TailReturn proc.spec.body ∧
    MustReturn proc.spec.body ∧
    sgenVCFull proc.verifyEnv proc.spec

theorem exportSound_of_mem {u : VSU} {proc : VerifiedProc} (hmem : proc ∈ u.exports) :
    exportSound u proc.spec.name := by
  refine ⟨proc, findProcByName_of_mem u.exports_nodup hmem, ?_⟩
  exact proc.sound

theorem resolve_import {provider consumer : VSU} (hcover : provider.importsResolvedBy consumer)
    {name : String} (hmem : name ∈ consumer.imports) :
    ∃ proc, proc ∈ provider.exports ∧ proc.spec.name = name := by
  have hname : name ∈ provider.exportNames := hcover name hmem
  rcases List.mem_map.mp hname with ⟨proc, hproc, hEq⟩
  exact ⟨proc, hproc, hEq⟩

end VSU

end HeytingLean.LeanCP.Modular
