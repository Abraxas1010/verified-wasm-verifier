import Mathlib.Data.Real.Basic
import Batteries.Data.List.Basic
import HeytingLean.Math.ProbVec

/-!
# QAI (Real-typed variants)

Standalone Real-typed versions of posterior/predictObs using ProbVec.normalizeR.
These are proof-friendly scaffolds and do not affect the Float-based CLI.
-/

namespace HeytingLean
namespace Quantum
namespace ActiveInference

open HeytingLean.Math

structure DiscreteModelR where
  ns : Nat
  no : Nat
  na : Nat
  prior : Array ℝ
  like  : Array (Array (Array ℝ)) -- like[a][s][o]


noncomputable def posteriorR (m : DiscreteModelR) (a : Nat) (obs : Nat) : Array ℝ :=
  let tab := m.like[a]!
  let outL : List ℝ := (List.range m.ns).map (fun s => m.prior[s]! * tab[s]![obs]!)
  List.toArray (ProbVec.normalizeListR outL)

noncomputable def predictObsR (m : DiscreteModelR) (a : Nat) : Array ℝ :=
  let tab := m.like[a]!
  let outL : List ℝ := (List.range m.no).map (fun o =>
    ((List.range m.ns).foldl (init := (0 : ℝ)) (fun acc st => acc + m.prior[st]! * tab[st]![o]!)))
  List.toArray (ProbVec.normalizeListR outL)

/-! ### Normalization properties (sum = 1 when nonempty) -/

def isNormalized (xs : Array ℝ) : Prop := xs.size ≠ 0 → ProbVec.sum xs = 1

lemma posteriorR_sum1 (m : DiscreteModelR) (a obs : Nat)
    (hns : m.ns ≠ 0) : ProbVec.sum (posteriorR m a obs) = 1 := by
  classical
  unfold posteriorR
  have hlen_ne : (List.range m.ns).length ≠ 0 := by
    have : m.ns ≠ 0 := hns
    simpa [List.length_range] using this
  have hne : ((List.range m.ns).map (fun s => m.prior[s]! * (m.like[a]![s]![obs]!))) ≠ [] := by
    intro contra
    have len0 : ((List.range m.ns).map (fun s => m.prior[s]! * (m.like[a]![s]![obs]!))).length = 0 := by
      simpa [contra]
    have : (List.range m.ns).length = 0 := by simpa [List.length_map] using len0
    exact hlen_ne this
  have : ProbVec.sumList (ProbVec.normalizeListR ((List.range m.ns).map (fun s => m.prior[s]! * (m.like[a]![s]![obs]!)))) = 1 :=
    ProbVec.normalizeList_sum1_of_nonempty hne
  simpa [ProbVec.sum, List.toList_toArray]
    using this

lemma predictObsR_sum1 (m : DiscreteModelR) (a : Nat)
    (hno : m.no ≠ 0) : ProbVec.sum (predictObsR m a) = 1 := by
  classical
  unfold predictObsR
  have hlen_ne : (List.range m.no).length ≠ 0 := by
    have : m.no ≠ 0 := hno
    simpa [List.length_range] using this
  have hne : ((List.range m.no).map (fun o =>
        (List.range m.ns).foldl (init := (0 : ℝ)) (fun acc st => acc + m.prior[st]! * (m.like[a]![st]![o]!)))) ≠ [] := by
    intro contra
    have len0 : ((List.range m.no).map (fun o =>
        (List.range m.ns).foldl (init := (0 : ℝ)) (fun acc st => acc + m.prior[st]! * (m.like[a]![st]![o]!)))).length = 0 := by
      simpa [contra]
    have : (List.range m.no).length = 0 := by simpa [List.length_map] using len0
    exact hlen_ne this
  have : ProbVec.sumList (ProbVec.normalizeListR ((List.range m.no).map (fun o =>
      (List.range m.ns).foldl (init := (0 : ℝ)) (fun acc st => acc + m.prior[st]! * (m.like[a]![st]![o]!))))) = 1 :=
    ProbVec.normalizeList_sum1_of_nonempty hne
  simpa [ProbVec.sum, List.toList_toArray]
    using this

end ActiveInference
end Quantum
end HeytingLean
