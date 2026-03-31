import HeytingLean.Numbers.Surreal.IR.CoqExport

/-!
# Sanity checks: Coq IR export for finite LoF programs
-/

namespace HeytingLean.Tests.Numbers.SurrealCoqIRSanity

open HeytingLean.Numbers.Surreal.LoFProgram
open HeytingLean.Numbers.Surreal.IR

private def toyProgram : Program :=
  { ops := #[Op.unmark, Op.mark [0] []], root := 1 }

example : (toCoqIR toyProgram).root = 1 := by
  decide

example : (toCoqIR toyProgram).operations.length = 2 := by
  decide

end HeytingLean.Tests.Numbers.SurrealCoqIRSanity

