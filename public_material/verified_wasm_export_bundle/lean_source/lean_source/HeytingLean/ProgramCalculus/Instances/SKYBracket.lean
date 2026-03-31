import HeytingLean.ProgramCalculus.Futamura
import HeytingLean.LoF.Combinators.PartialEval

/-!
# ProgramCalculus.Instances.SKYBracket

Concrete `ProgramCalculus` instance for the SKY/Bracket layer:

* Programs are `Bracket.CExp` with two variables `code` and `input`.
* Inputs are `(codeComb × inputComb)`, split as static `codeComb` + dynamic `inputComb`.
* `Mix` specializes by substituting `code` with a closed SKY term (`Comb`) via `substComb`.
-/

namespace HeytingLean
namespace ProgramCalculus
namespace Instances

open HeytingLean.LoF
open HeytingLean.LoF.Combinators

inductive SKYCI where
  | code
  | input
deriving DecidableEq, Repr

def skyBracketLanguage (fuel : Nat) : Language where
  Program := HeytingLean.LoF.Combinators.Bracket.CExp SKYCI
  Input := Comb × Comb
  Output := Comb
  eval := fun program input =>
    let (code, x) := input
    let env : SKYCI → Comb
      | .code => code
      | .input => x
    SKYExec.reduceFuel fuel (Bracket.CExp.denote env program)

def skyBracketSplit : SplitInput (Comb × Comb) where
  Static := Comb
  Dynamic := Comb
  pack := Prod.mk

def skyBracketMix (fuel : Nat) :
    Mix (skyBracketLanguage fuel) skyBracketSplit where
  Residual := Bracket.CExp SKYCI
  evalResidual := fun residual x =>
    let dynamic : SKYCI → Comb
      | .code => Comb.K
      | .input => x
    SKYExec.reduceFuel fuel (Bracket.CExp.denote dynamic residual)
  apply := fun program code =>
    let static : SKYCI → Option Comb
      | .code => some code
      | .input => none
    Bracket.CExp.substComb (Var := SKYCI) static program
  correct := by
    intro program code x
    let static : SKYCI → Option Comb
      | .code => some code
      | .input => none
    let dynamic : SKYCI → Comb
      | .code => Comb.K
      | .input => x
    let env : SKYCI → Comb
      | .code => code
      | .input => x
    have hmerge : Bracket.CExp.mergeEnv static dynamic = env := by
      funext v
      cases v <;> rfl
    have hdenote :
        Bracket.CExp.denote dynamic (Bracket.CExp.substComb (Var := SKYCI) static program) =
          Bracket.CExp.denote env program := by
      simpa [hmerge] using
        (Bracket.CExp.denote_substComb (Var := SKYCI) (static := static) (dynamic := dynamic) (e := program))
    simpa [skyBracketLanguage, skyBracketSplit, static, dynamic, env] using
      congrArg (SKYExec.reduceFuel fuel) hdenote

def skyBracketCodeSem (fuel : Nat) (code x : Comb) : Comb :=
  SKYExec.reduceFuel fuel (Comb.app code x)

def skyBracketInterp : Bracket.CExp SKYCI :=
  Bracket.CExp.app (.var .code) (.var .input)

def skyBracketInterpModel (fuel : Nat) :
    InterpModel (skyBracketLanguage fuel) skyBracketSplit where
  codeSem := skyBracketCodeSem fuel
  interp := skyBracketInterp
  correct := by
    intro code x
    simp [skyBracketLanguage, skyBracketSplit, skyBracketCodeSem, skyBracketInterp, Bracket.CExp.denote]

end Instances
end ProgramCalculus
end HeytingLean
