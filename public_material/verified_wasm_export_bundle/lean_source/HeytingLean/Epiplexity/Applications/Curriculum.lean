import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Perm.Basic
import HeytingLean.Cybernetics.Feedback
import HeytingLean.Epiplexity.Prelude
import HeytingLean.Probability.InfoTheory.FinDist

namespace HeytingLean
namespace Epiplexity
namespace Applications

universe u

open HeytingLean.Probability.InfoTheory

/-- A finite-first curriculum: a fixed-length ordered dataset (indexed by `Fin m`). -/
abbrev Curriculum (D : Type u) (m : Nat) := Fin m → D

namespace Curriculum

variable {D : Type u} {m : Nat}

def toList (c : Curriculum D m) : List D :=
  List.ofFn c

/-- Two curricula are equivalent if they contain the same data, up to permutation. -/
def PermEq (c₁ c₂ : Curriculum D m) : Prop :=
  (toList c₁).Perm (toList c₂)

@[refl] theorem permEq_refl (c : Curriculum D m) : PermEq c c := by
  dsimp [PermEq, toList]
  exact List.Perm.refl _

@[symm] theorem permEq_symm {c₁ c₂ : Curriculum D m} : PermEq c₁ c₂ → PermEq c₂ c₁ := by
  intro h
  exact h.symm

@[trans] theorem permEq_trans {c₁ c₂ c₃ : Curriculum D m} :
    PermEq c₁ c₂ → PermEq c₂ c₃ → PermEq c₁ c₃ := by
  intro h₁₂ h₂₃
  exact h₁₂.trans h₂₃

end Curriculum

/-- Execute a curriculum as a left-fold of an update rule. -/
def runCurriculum {Sys D : Type u} (update : Sys → D → Sys) (s0 : Sys) {m : Nat}
    (c : Curriculum D m) : Sys :=
  (Curriculum.toList c).foldl update s0

/-- Package a training update as a cybernetics feedback step. -/
def curriculumAsFeedback {Sys D : Type u} (update : Sys → D → Sys) :
    HeytingLean.Cybernetics.Feedback Sys D :=
  { step := update }

namespace CurriculumEpiplexity

variable {Sys D : Type u} {m : Nat} [Fintype D] [Fintype Sys] [Nonempty D]

/-- Uniform distribution over curricula of fixed length `m`. -/
noncomputable def uniformCurricula : FinDist (Curriculum D m) :=
  Epiplexity.FinDist.uniform (α := Curriculum D m)

def learn (update : Sys → D → Sys) (s0 : Sys) (c : Curriculum D m) : Sys :=
  runCurriculum (Sys := Sys) (D := D) update s0 c

/-- Output distribution induced by sampling a curriculum uniformly and running a deterministic learner. -/
noncomputable def outputDist (update : Sys → D → Sys) (s0 : Sys) : FinDist Sys :=
  FinDist.map (f := learn (Sys := Sys) (D := D) (m := m) update s0) uniformCurricula

end CurriculumEpiplexity

end Applications
end Epiplexity
end HeytingLean

