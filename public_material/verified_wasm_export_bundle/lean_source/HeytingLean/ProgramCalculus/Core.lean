/-!
# ProgramCalculus.Core

Minimal, interface-first scaffolding for talking about “programs”, semantics, and input-splitting.

This slice is intentionally small: most of the repo already contains concrete “languages”:

* `HeytingLean.LambdaIR` (typed terms + `LambdaIR.eval`)
* `HeytingLean.LoF.LoFPrimary` (LoF expressions + `LoFPrimary.eval`)
* `HeytingLean.LoF.Combinators` (SKY terms + rewrite semantics)

The goal here is to provide a common *interface* so Futamura-style statements can be phrased
once and instantiated many times.
-/

namespace HeytingLean
namespace ProgramCalculus

/-- A tiny denotational interface: programs with an evaluator. -/
structure Language where
  Program : Type
  Input : Type
  Output : Type
  eval : Program → Input → Output

/-- Observational equivalence of programs (semantic equality). -/
def ObsEq (language : Language) (p q : language.Program) : Prop :=
  ∀ input : language.Input, language.eval p input = language.eval q input

/-- Split an input into a static part and a dynamic part, with a packing function. -/
structure SplitInput (input : Type) where
  Static : Type
  Dynamic : Type
  pack : Static → Dynamic → input

end ProgramCalculus
end HeytingLean

