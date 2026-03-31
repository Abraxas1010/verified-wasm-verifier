import HeytingLean.InqBQ.HardnessRegistry

namespace HeytingLean.Tests.InqBQ

open HeytingLean.InqBQ

example : hardnessRegistry.length = 2 := by simp

example :
    findEntryByBenchmarkId? "h10upc_finite_validity_family" = some finiteValidityFamilyEntry := by
  simp

example :
    findEntryByBenchmarkId? "h10upc_inqbq_validity_family" = some inqbqValidityFamilyEntry := by
  simp

example :
    (findMetaByBenchmarkId? "h10upc_finite_validity_family").map (·.sourceTheorem) =
      some "finite_validity_family_not_re" := by
  simp [finiteValidityFamilyEntry]

example :
    (findMetaByBenchmarkId? "h10upc_inqbq_validity_family").map (·.predicateFamily) =
      some "inqbqValidityFamily" := by
  simp [inqbqValidityFamilyEntry]

example : ¬ REPred finiteValidityFamily :=
  finiteValidityFamilyEntry.notRe

example : ¬ REPred inqbqValidityFamily :=
  inqbqValidityFamilyEntry.notRe

example :
    ∃ entry ∈ hardnessRegistry, entry.predicate = finiteValidityFamily := by
  exact registry_contains_finiteValidityFamily

example :
    ∃ entry ∈ hardnessRegistry, entry.predicate = inqbqValidityFamily := by
  exact registry_contains_inqbqValidityFamily

end HeytingLean.Tests.InqBQ
