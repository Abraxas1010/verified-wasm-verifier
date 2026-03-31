import HeytingLean.InqBQ.NonREEndpoint

namespace HeytingLean
namespace InqBQ

open Nat.Partrec

structure HardnessRegistryMeta where
  benchmarkId : String
  sourceTheorem : String
  sourceModule : String
  predicateFamily : String
  formulaInstances : String
  knownSemanticStatus : String
deriving Repr, DecidableEq

structure HardnessRegistryEntry extends HardnessRegistryMeta where
  predicate : List H10UPC → Prop
  notRe : ¬ REPred predicate

def finiteValidityFamilyEntry : HardnessRegistryEntry where
  benchmarkId := "h10upc_finite_validity_family"
  sourceTheorem := "finite_validity_family_not_re"
  sourceModule := "HeytingLean.InqBQ.FragmentHardness"
  predicateFamily := "finiteValidityFamily"
  formulaInstances := "h10upcFiniteValidityFormula cs over ReductionSig"
  knownSemanticStatus := "not recursively enumerable"
  predicate := finiteValidityFamily
  notRe := finite_validity_family_not_re

def inqbqValidityFamilyEntry : HardnessRegistryEntry where
  benchmarkId := "h10upc_inqbq_validity_family"
  sourceTheorem := "inqbq_validity_family_not_re"
  sourceModule := "HeytingLean.InqBQ.NonREEndpoint"
  predicateFamily := "inqbqValidityFamily"
  formulaInstances := "reductionValidityFormula cs over ABSignature ReductionSig"
  knownSemanticStatus := "not recursively enumerable"
  predicate := inqbqValidityFamily
  notRe := inqbq_validity_family_not_re

def hardnessRegistry : List HardnessRegistryEntry :=
  [finiteValidityFamilyEntry, inqbqValidityFamilyEntry]

def hardnessRegistryMeta : List HardnessRegistryMeta :=
  hardnessRegistry.map HardnessRegistryEntry.toHardnessRegistryMeta

def findEntryByBenchmarkId? (benchmarkId : String) : Option HardnessRegistryEntry :=
  hardnessRegistry.find? (fun entry => entry.benchmarkId == benchmarkId)

def findMetaByBenchmarkId? (benchmarkId : String) : Option HardnessRegistryMeta :=
  (findEntryByBenchmarkId? benchmarkId).map HardnessRegistryEntry.toHardnessRegistryMeta

@[simp] theorem hardnessRegistry_length : hardnessRegistry.length = 2 := rfl

@[simp] theorem findEntryByBenchmarkId?_finiteValidity :
    findEntryByBenchmarkId? "h10upc_finite_validity_family" = some finiteValidityFamilyEntry := by
  simp [findEntryByBenchmarkId?, hardnessRegistry, finiteValidityFamilyEntry, inqbqValidityFamilyEntry]

@[simp] theorem findEntryByBenchmarkId?_inqbqValidity :
    findEntryByBenchmarkId? "h10upc_inqbq_validity_family" = some inqbqValidityFamilyEntry := by
  simp [findEntryByBenchmarkId?, hardnessRegistry, finiteValidityFamilyEntry, inqbqValidityFamilyEntry]

@[simp] theorem findMetaByBenchmarkId?_finiteValidity :
    findMetaByBenchmarkId? "h10upc_finite_validity_family" =
      some finiteValidityFamilyEntry.toHardnessRegistryMeta := by
  simp [findMetaByBenchmarkId?]

@[simp] theorem findMetaByBenchmarkId?_inqbqValidity :
    findMetaByBenchmarkId? "h10upc_inqbq_validity_family" =
      some inqbqValidityFamilyEntry.toHardnessRegistryMeta := by
  simp [findMetaByBenchmarkId?]

theorem finiteValidityFamilyEntry_mem : finiteValidityFamilyEntry ∈ hardnessRegistry := by
  simp [hardnessRegistry]

theorem inqbqValidityFamilyEntry_mem : inqbqValidityFamilyEntry ∈ hardnessRegistry := by
  simp [hardnessRegistry]

theorem registry_contains_finiteValidityFamily :
    ∃ entry ∈ hardnessRegistry, entry.predicate = finiteValidityFamily := by
  exact ⟨finiteValidityFamilyEntry, finiteValidityFamilyEntry_mem, rfl⟩

theorem registry_contains_inqbqValidityFamily :
    ∃ entry ∈ hardnessRegistry, entry.predicate = inqbqValidityFamily := by
  exact ⟨inqbqValidityFamilyEntry, inqbqValidityFamilyEntry_mem, rfl⟩

end InqBQ
end HeytingLean
