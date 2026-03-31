import HeytingLean.Genesis.EigenformSoup.DAOF

/-!
# Genesis.EigenformSoup.TransitionDensity

DAOF transition-density facts used by LES ATP targeting.
-/

namespace HeytingLean.Genesis.EigenformSoup

theorem daofMapNucleus_idempotent (c : DAOFClass) :
    daofMapNucleus (daofMapNucleus c) = daofMapNucleus c := by
  cases c <;> rfl

theorem daofMapNucleus_rank_mono (c : DAOFClass) :
    c.rank ≤ (daofMapNucleus c).rank := by
  cases c <;> decide

theorem classifyByGap_eq_formless_iff (carrier gap nearThreshold : Nat) :
    classifyByGap carrier gap nearThreshold = .formless ↔ carrier = 0 := by
  constructor
  · intro h
    by_cases hcarrier : carrier = 0
    · exact hcarrier
    · simp [classifyByGap, hcarrier] at h
      split_ifs at h
  · intro hcarrier
    simp [classifyByGap, hcarrier]

theorem classifyByGap_eq_distinguished_iff
    (carrier gap nearThreshold : Nat)
    (hcarrier : carrier ≠ 0) :
    classifyByGap carrier gap nearThreshold = .distinguished ↔ gap = 0 := by
  constructor
  · intro h
    by_cases hgap : gap = 0
    · exact hgap
    · simp [classifyByGap, hcarrier, hgap] at h
      split_ifs at h
  · intro hgap
    simp [classifyByGap, hcarrier, hgap]

theorem classifyByGap_rank_of_large_gap
    (carrier gap nearThreshold : Nat)
    (hcarrier : carrier ≠ 0)
    (hgap : gap ≠ 0)
    (hlarge : nearThreshold < gap) :
    (classifyByGap carrier gap nearThreshold).rank = 1 := by
  rw [classifyByGap_obscure_of_large_gap carrier gap nearThreshold hcarrier hgap hlarge]
  rfl

theorem classifyByGap_rank_of_near_threshold
    (carrier gap nearThreshold : Nat)
    (hcarrier : carrier ≠ 0)
    (hgap : gap ≠ 0)
    (hnear : gap ≤ nearThreshold) :
    (classifyByGap carrier gap nearThreshold).rank = 2 := by
  rw [classifyByGap_ambiguous_of_near_threshold carrier gap nearThreshold hcarrier hgap hnear]
  rfl

theorem classifyByGap_gapNucleus_rank_mono
    (carrier gap nearThreshold : Nat)
    (hnear : nearThreshold ≠ 0) :
    (classifyByGap carrier gap nearThreshold).rank ≤
      (classifyByGap carrier (gapNucleus nearThreshold gap) nearThreshold).rank := by
  have hnat := classifyByGap_gapNucleus_naturality carrier gap nearThreshold hnear
  rw [hnat]
  exact daofMapNucleus_rank_mono (classifyByGap carrier gap nearThreshold)

end HeytingLean.Genesis.EigenformSoup
