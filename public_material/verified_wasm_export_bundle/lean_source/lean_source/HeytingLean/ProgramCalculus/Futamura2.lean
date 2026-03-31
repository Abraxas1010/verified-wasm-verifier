import HeytingLean.ProgramCalculus.Futamura

/-!
# ProgramCalculus.Futamura2

Scaffolding for the second Futamura projection (self-application).

The base `ProgramCalculus.Futamura` file is intentionally generic and does not assume
programs-as-data. This module records a *sufficient interface* for self-application and defines
the second projection term.
-/

namespace HeytingLean
namespace ProgramCalculus

/-- A self-applicable `Mix` can represent itself as a program and decode its own residuals. -/
structure SelfApplicableMix (language : Language) (split : SplitInput language.Input)
    extends Mix language split where
  /-- The mix/specializer represented as a program in the object language. -/
  mixAsProgram : language.Program
  /-- Encoding of programs as static inputs. -/
  encodeProgram : language.Program → split.Static
  /-- An auxiliary encoding of static inputs as dynamic inputs (for self-application plumbing). -/
  encodeStatic : split.Static → split.Dynamic
  /-- Decode a residual program from an output value. -/
  decodeResidual : language.Output → toMix.Residual
  /-- Correctness of self-application (interface-level). -/
  self_apply_correct :
    ∀ (program : language.Program) (static : split.Static),
      decodeResidual (language.eval mixAsProgram
        (split.pack (encodeProgram program) (encodeStatic static))) =
        toMix.apply program static

/-- Second Futamura projection: `compiler = mix(mix, interp)`. -/
def futamura2
    {language : Language}
    {split : SplitInput language.Input}
    (mix : SelfApplicableMix language split)
    (model : InterpModel language split) :
    mix.toMix.Residual :=
  mix.toMix.apply mix.mixAsProgram (mix.encodeProgram model.interp)

/-- Placeholder correctness hook for the second projection (reflexive equality). -/
theorem futamura2_correct
    {language : Language}
    {split : SplitInput language.Input}
    (mix : SelfApplicableMix language split)
    (model : InterpModel language split)
    (_code : split.Static) :
    futamura2 mix model = futamura2 mix model :=
  rfl

end ProgramCalculus
end HeytingLean

