import HeytingLean.ProgramCalculus.Core

/-!
# ProgramCalculus.Futamura

Interface-first Futamura scaffolding:

* `Mix` packages a partial evaluator (specializer) together with the “mix equation”
  as a correctness field.
* `InterpModel` packages an interpreter together with an intended semantics for codes.
* `compile` is specialization of an interpreter with respect to a fixed code, and
  `compile_correct` is the (semantic) First Futamura Projection.

This file stays generic and does **not** assume programs-as-data inside the object language.
Second/third projections (self-application) are therefore treated as later milestones.
-/

namespace HeytingLean
namespace ProgramCalculus

/-- A partial evaluator for programs whose inputs are split into static+dynamic parts.

The result type `Residual` is allowed to differ from the original `Program` type:
specialization typically reduces the dynamic arity (e.g. `n+1` inputs → `n` inputs). -/
structure Mix (language : Language) (split : SplitInput language.Input) where
  Residual : Type
  evalResidual : Residual → split.Dynamic → language.Output
  apply : language.Program → split.Static → Residual
  correct :
    ∀ (program : language.Program) (static : split.Static) (dynamic : split.Dynamic),
      evalResidual (apply program static) dynamic =
        language.eval program (split.pack static dynamic)

/-- An interpreter model: an interpreter program together with an intended semantics for codes.

This keeps “source language” abstract: the semantics `codeSem` is just a function of a code
and a dynamic input. -/
structure InterpModel (language : Language) (split : SplitInput language.Input) where
  codeSem : split.Static → split.Dynamic → language.Output
  interp : language.Program
  correct :
    ∀ (code : split.Static) (input : split.Dynamic),
      language.eval interp (split.pack code input) = codeSem code input

/-- Compiler-by-specialization: compile a code by specializing the interpreter to that code. -/
def compile {language : Language} {split : SplitInput language.Input}
    (mix : Mix language split) (model : InterpModel language split) (code : split.Static) :
    mix.Residual :=
  mix.apply model.interp code

/-- First Futamura projection (semantic): specialized interpreter matches intended code semantics. -/
theorem compile_correct {language : Language} {split : SplitInput language.Input}
    (mix : Mix language split) (model : InterpModel language split)
    (code : split.Static) (input : split.Dynamic) :
    mix.evalResidual (compile mix model code) input = model.codeSem code input := by
  have h1 :=
    mix.correct (program := model.interp) (static := code) (dynamic := input)
  have h2 := model.correct (code := code) (input := input)
  exact (h1.trans h2)

end ProgramCalculus
end HeytingLean
