import HeytingLean.Constructor.CT.TaskExistence
import HeytingLean.Crypto.QKD.BB84.Tasks

/-!
# BB84 constructor model (`TaskCT`)

We build a constructor-existence model for the BB84 substrate in which:
- basis-restricted copy tasks (`copyZ`, `copyX`) are possible (constructors exist);
- universal copying (`copyAll`) is impossible (no constructor implements it).

The model is interface-first: we do not formalize measurement semantics, only a
syntactic “allowed arcs” invariant that excludes universal cloning.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84

open HeytingLean.Constructor.CT

/-!
## Allowed arcs

An arc is allowed if it stays within one basis, or prepares/measures into one basis.
This set includes the arcs of our primitive tasks, and is closed under `Task.seq/par`
because those operations are list concatenation at the syntax layer.
-/

def AllowedArc : (Attribute BB84Substrate × Attribute BB84Substrate) → Prop
  | (inp, out) =>
      (inp = attrZBasis ∧ out = attrZBasis) ∨
      (inp = attrXBasis ∧ out = attrXBasis) ∨
      (inp = Set.univ ∧ out = attrZBasis) ∨
      (inp = Set.univ ∧ out = attrXBasis)

lemma copyAll_arc_not_allowed : ¬ AllowedArc (attrAll, attrAll) := by
  intro h
  rcases h with ⟨hin, hout⟩ | ⟨hin, hout⟩ | ⟨hin, hout⟩ | ⟨hin, hout⟩
  · exact attrAll_ne_attrZBasis hin
  · exact attrAll_ne_attrXBasis hin
  · exact attrAll_ne_attrZBasis hout
  · exact attrAll_ne_attrXBasis hout

/-!
## Constructor type and implementation relation
-/

inductive BB84Ctor : Type
  | id
  | copyZ
  | copyX
  | prepZ
  | prepX
  | measZ
  | measX
  | seq (c₁ c₂ : BB84Ctor)
  | par (c₁ c₂ : BB84Ctor)

inductive BB84Implements : BB84Ctor → CTask BB84Substrate → Prop
  | id : BB84Implements BB84Ctor.id { arcs := [] }
  | copyZ : BB84Implements BB84Ctor.copyZ copyZ
  | copyX : BB84Implements BB84Ctor.copyX copyX
  | prepZ : BB84Implements BB84Ctor.prepZ prepareZ
  | prepX : BB84Implements BB84Ctor.prepX prepareX
  | measZ : BB84Implements BB84Ctor.measZ measureZ
  | measX : BB84Implements BB84Ctor.measX measureX
  | seq {c₁ c₂ : BB84Ctor} {T U : CTask BB84Substrate} :
      BB84Implements c₁ T → BB84Implements c₂ U →
        BB84Implements (BB84Ctor.seq c₁ c₂) (Task.seq T U)
  | par {c₁ c₂ : BB84Ctor} {T U : CTask BB84Substrate} :
      BB84Implements c₁ T → BB84Implements c₂ U →
        BB84Implements (BB84Ctor.par c₁ c₂) (Task.par T U)

/-!
## No universal cloning
-/

lemma bb84_implements_allowed_arcs {c : BB84Ctor} {T : CTask BB84Substrate} :
    BB84Implements c T → ∀ a, a ∈ T.arcs → AllowedArc a := by
  intro hImpl
  induction hImpl with
  | id =>
    intro a ha
    -- Note: `List.Mem` over `[]` has no constructors; `cases ha` avoids
    -- `unnecessarySimpa`/`unusedTactic` linter warnings under `--wfail`.
    cases ha
  | copyZ =>
    intro a ha
    have ha' : a = (attrZBasis, attrZBasis) := by
      simpa [copyZ] using ha
    cases ha'
    simp [AllowedArc]
  | copyX =>
    intro a ha
    have ha' : a = (attrXBasis, attrXBasis) := by
      simpa [copyX] using ha
    cases ha'
    simp [AllowedArc]
  | prepZ =>
    intro a ha
    have ha' : a = (Set.univ, attrZBasis) := by
      simpa [prepareZ] using ha
    cases ha'
    simp [AllowedArc]
  | prepX =>
    intro a ha
    have ha' : a = (Set.univ, attrXBasis) := by
      simpa [prepareX] using ha
    cases ha'
    simp [AllowedArc]
  | measZ =>
    intro a ha
    have ha' : a = (attrAll, attrZBasis) := by
      simpa [measureZ] using ha
    cases ha'
    -- `attrAll = Set.univ`, so this matches the prepare/measure allowed arc.
    simp [AllowedArc, attrAll, BB84State.allStates]
  | measX =>
    intro a ha
    have ha' : a = (attrAll, attrXBasis) := by
      simpa [measureX] using ha
    cases ha'
    simp [AllowedArc, attrAll, BB84State.allStates]
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

theorem not_implements_copyAll (c : BB84Ctor) : ¬ BB84Implements c copyAll := by
  intro h
  have hAllowed : AllowedArc (attrAll, attrAll) := by
    apply bb84_implements_allowed_arcs h
    simp [copyAll]
  exact copyAll_arc_not_allowed hAllowed

/-!
## `TaskCT` instance
-/

def bb84TaskCT : TaskCT BB84Substrate where
  Ctor := BB84Ctor
  implements := BB84Implements
  seqCtor := BB84Ctor.seq
  parCtor := BB84Ctor.par
  implements_seq := fun h1 h2 => BB84Implements.seq h1 h2
  implements_par := fun h1 h2 => BB84Implements.par h1 h2

theorem copyZ_possible : bb84TaskCT.possible copyZ :=
  ⟨BB84Ctor.copyZ, BB84Implements.copyZ⟩

theorem copyX_possible : bb84TaskCT.possible copyX :=
  ⟨BB84Ctor.copyX, BB84Implements.copyX⟩

theorem copyAll_impossible : bb84TaskCT.impossible copyAll := by
  intro ⟨c, hc⟩
  exact not_implements_copyAll c hc

end BB84
end QKD
end Crypto
end HeytingLean
