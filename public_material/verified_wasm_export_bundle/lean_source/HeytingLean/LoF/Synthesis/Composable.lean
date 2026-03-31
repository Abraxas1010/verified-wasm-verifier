import HeytingLean.ProgramCalculus.Core

/-!
# Synthesis.Composable

Interface-first scaffolding for “quotient + residual” decomposition of programs/proofs.

This file intentionally does **not** implement an anti-unification algorithm. It only defines
the data you ultimately want to produce (and verify) when doing proof/program “division”:

* a quotient block,
* a residual block,
* and a recombination operator that reconstructs the original semantics.
-/

namespace HeytingLean
namespace LoF
namespace Synthesis

open HeytingLean.ProgramCalculus

/-- A “block” in a compositional synthesis story: a program plus interface metadata. -/
structure Block (language : Language) where
  program : language.Program
  needs : Type
  provides : Type

/-- A quotient/residual decomposition together with a semantic reconstruction law. -/
structure Decomposition (language : Language) where
  original : language.Program
  quotient : language.Program
  residual : language.Program
  recombine : language.Program → language.Program → language.Program
  sound : ObsEq language (recombine quotient residual) original

end Synthesis
end LoF
end HeytingLean

