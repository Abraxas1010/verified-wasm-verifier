import Mathlib

/-!
# Genesis.EigenformSoup.DAOF

DAOF (Distinguished, Ambiguous, Obscure, Formless) classification surface for
LES-Omega instrumentation and theorem-facing contracts.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Four-valued DAOF regime order. -/
inductive DAOFClass
  | formless
  | obscure
  | ambiguous
  | distinguished
deriving DecidableEq, Repr

/-- Numeric embedding of DAOF order. -/
def DAOFClass.rank : DAOFClass → Nat
  | .formless => 0
  | .obscure => 1
  | .ambiguous => 2
  | .distinguished => 3

/--
Classify from carrier/gap observables:
- empty carrier is `formless`
- zero gap is `distinguished`
- nonzero gap above threshold is `obscure`
- nonzero gap below threshold is `ambiguous`
-/
def classifyByGap (carrier gap nearThreshold : Nat) : DAOFClass :=
  if carrier = 0 then
    .formless
  else if gap = 0 then
    .distinguished
  else if nearThreshold < gap then
    .obscure
  else
    .ambiguous

/-- Canonical DAOF morphism induced by near-threshold gap clipping. -/
def daofMapNucleus : DAOFClass → DAOFClass
  | .obscure => .ambiguous
  | c => c

/-- Gap-space clipping nucleus used by DAOF naturality statements. -/
def gapNucleus (nearThreshold gap : Nat) : Nat :=
  Nat.min gap nearThreshold

theorem classifyByGap_formless (gap nearThreshold : Nat) :
    classifyByGap 0 gap nearThreshold = .formless := by
  simp [classifyByGap]

theorem classifyByGap_distinguished_of_gap_zero
    (carrier nearThreshold : Nat) (hcarrier : carrier ≠ 0) :
    classifyByGap carrier 0 nearThreshold = .distinguished := by
  simp [classifyByGap, hcarrier]

theorem classifyByGap_obscure_of_large_gap
    (carrier gap nearThreshold : Nat)
    (hcarrier : carrier ≠ 0)
    (hgap : gap ≠ 0)
    (hlarge : nearThreshold < gap) :
    classifyByGap carrier gap nearThreshold = .obscure := by
  simp [classifyByGap, hcarrier, hgap, hlarge]

theorem classifyByGap_ambiguous_of_near_threshold
    (carrier gap nearThreshold : Nat)
    (hcarrier : carrier ≠ 0)
    (hgap : gap ≠ 0)
    (hnear : gap ≤ nearThreshold) :
    classifyByGap carrier gap nearThreshold = .ambiguous := by
  have hnot : ¬ nearThreshold < gap := Nat.not_lt.mpr hnear
  simp [classifyByGap, hcarrier, hgap, hnot]

/--
Naturality (clipping form): classifying after applying the gap-clipping nucleus
is equivalent to classifying first and mapping by `daofMapNucleus`.

Assumption `nearThreshold ≠ 0` matches LES-Omega instrumentation where
near-threshold windows are strictly positive.
-/
theorem classifyByGap_gapNucleus_naturality
    (carrier gap nearThreshold : Nat)
    (hnear : nearThreshold ≠ 0) :
    classifyByGap carrier (gapNucleus nearThreshold gap) nearThreshold =
      daofMapNucleus (classifyByGap carrier gap nearThreshold) := by
  by_cases hcarrier : carrier = 0
  · simp [classifyByGap, hcarrier, daofMapNucleus]
  · by_cases hgap : gap = 0
    · simp [classifyByGap, hcarrier, hgap, gapNucleus, daofMapNucleus]
    · by_cases hlarge : nearThreshold < gap
      · have hmin : gapNucleus nearThreshold gap = nearThreshold := by
          simp [gapNucleus, Nat.le_of_lt hlarge]
        have hnearGap : nearThreshold ≠ 0 := hnear
        simp [classifyByGap, hcarrier, hgap, hlarge, hmin, daofMapNucleus, hnearGap]
      · have hle : gap ≤ nearThreshold := Nat.le_of_not_gt hlarge
        have hmin : gapNucleus nearThreshold gap = gap := by
          simp [gapNucleus, hle]
        have hnotlarge : ¬ nearThreshold < gap := hlarge
        simp [classifyByGap, hcarrier, hgap, hnotlarge, hmin, daofMapNucleus]

end HeytingLean.Genesis.EigenformSoup
