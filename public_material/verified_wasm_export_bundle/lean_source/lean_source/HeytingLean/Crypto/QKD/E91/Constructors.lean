import HeytingLean.Constructor.CT.TaskExistence
import HeytingLean.Crypto.QKD.E91.Tasks

/-!
# E91 constructor model (`TaskCT`, toy)

This mirrors the BB84 pattern:
- copying within each context is possible,
- copying the combined “key ∪ test” alphabet is impossible (no constructor).

The physics meaning is: “if you could universally copy the states used across key
generation and CHSH testing, you could eavesdrop without being detected.”  The
full CHSH story is a future refinement; this file provides a *non-trivial CT
instance* that supports compositional security theorems today.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91

open HeytingLean.Constructor.CT

def AllowedArc : (Attribute E91Substrate × Attribute E91Substrate) → Prop
  | (inp, out) =>
      (inp = attrKey ∧ out = attrKey) ∨
      (inp = attrTest ∧ out = attrTest) ∨
      (inp = Set.univ ∧ out = attrKey) ∨
      (inp = Set.univ ∧ out = attrTest)

lemma copyAll_arc_not_allowed : ¬ AllowedArc (attrAll, attrAll) := by
  intro h
  rcases h with ⟨hin, hout⟩ | ⟨hin, hout⟩ | ⟨hin, hout⟩ | ⟨hin, hout⟩
  · exact attrAll_ne_attrKey hin
  · exact attrAll_ne_attrTest hin
  · exact attrAll_ne_attrKey hout
  · exact attrAll_ne_attrTest hout

inductive E91Ctor : Type
  | id
  | copyKey
  | copyTest
  | prepKey
  | prepTest
  | seq (c₁ c₂ : E91Ctor)
  | par (c₁ c₂ : E91Ctor)

inductive E91Implements : E91Ctor → CTask E91Substrate → Prop
  | id : E91Implements E91Ctor.id { arcs := [] }
  | copyKey : E91Implements E91Ctor.copyKey copyKey
  | copyTest : E91Implements E91Ctor.copyTest copyTest
  | prepKey : E91Implements E91Ctor.prepKey prepareKey
  | prepTest : E91Implements E91Ctor.prepTest prepareTest
  | seq {c₁ c₂ : E91Ctor} {T U : CTask E91Substrate} :
      E91Implements c₁ T → E91Implements c₂ U →
        E91Implements (E91Ctor.seq c₁ c₂) (Task.seq T U)
  | par {c₁ c₂ : E91Ctor} {T U : CTask E91Substrate} :
      E91Implements c₁ T → E91Implements c₂ U →
        E91Implements (E91Ctor.par c₁ c₂) (Task.par T U)

lemma e91_implements_allowed_arcs {c : E91Ctor} {T : CTask E91Substrate} :
    E91Implements c T → ∀ a, a ∈ T.arcs → AllowedArc a := by
  intro hImpl
  induction hImpl with
  | id =>
      intro a ha
      cases ha
  | copyKey =>
      intro a ha
      have ha' : a = (attrKey, attrKey) := by
        simpa [copyKey] using ha
      cases ha'
      simp [AllowedArc]
  | copyTest =>
      intro a ha
      have ha' : a = (attrTest, attrTest) := by
        simpa [copyTest] using ha
      cases ha'
      simp [AllowedArc]
  | prepKey =>
      intro a ha
      have ha' : a = (Set.univ, attrKey) := by
        simpa [prepareKey] using ha
      cases ha'
      simp [AllowedArc]
  | prepTest =>
      intro a ha
      have ha' : a = (Set.univ, attrTest) := by
        simpa [prepareTest] using ha
      cases ha'
      simp [AllowedArc]
  | seq _ _ ihT ihU =>
      intro a ha
      rcases List.mem_append.1 (by simpa [Task.seq] using ha) with haT | haU
      · exact ihT a haT
      · exact ihU a haU
  | par _ _ ihT ihU =>
      intro a ha
      rcases List.mem_append.1 (by simpa [Task.par] using ha) with haT | haU
      · exact ihT a haT
      · exact ihU a haU

theorem not_implements_copyAll (c : E91Ctor) : ¬ E91Implements c copyAll := by
  intro h
  have hAllowed : AllowedArc (attrAll, attrAll) := by
    apply e91_implements_allowed_arcs h
    simp [copyAll]
  exact copyAll_arc_not_allowed hAllowed

def e91TaskCT : TaskCT E91Substrate where
  Ctor := E91Ctor
  implements := E91Implements
  seqCtor := E91Ctor.seq
  parCtor := E91Ctor.par
  implements_seq := fun h1 h2 => E91Implements.seq h1 h2
  implements_par := fun h1 h2 => E91Implements.par h1 h2

theorem copyKey_possible : e91TaskCT.possible copyKey :=
  ⟨E91Ctor.copyKey, E91Implements.copyKey⟩

theorem copyTest_possible : e91TaskCT.possible copyTest :=
  ⟨E91Ctor.copyTest, E91Implements.copyTest⟩

theorem copyAll_impossible : e91TaskCT.impossible copyAll := by
  intro ⟨c, hc⟩
  exact not_implements_copyAll c hc

end E91
end QKD
end Crypto
end HeytingLean

