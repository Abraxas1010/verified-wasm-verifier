import HeytingLean.Generative.IntNucleusKit
import HeytingLean.Numbers.Surreal.Nucleus
import HeytingLean.Numbers.Surreal.ReentryAdapter
import HeytingLean.Util.Iterate

namespace HeytingLean
namespace Tests
namespace Generative

open HeytingLean.Generative
open HeytingLean.Util
open HeytingLean.Numbers.Surreal
open HeytingLean.LoF

/-!
Compile-only smoke: `iterateUntilFix` on an interior nucleus.

We use the Surreal interior re-entry on `Set PreGame` and iterate the
interior action up to `k` steps, checking the types (#check) and that
the returned tuple shape matches expectations.
-/

def R := Surreal.surrealIntReentry

variable (S : Set HeytingLean.Numbers.PreGame)

-- One step function is the interior action itself.
def step : (Set HeytingLean.Numbers.PreGame) → (Set HeytingLean.Numbers.PreGame) :=
  (R).nucleus.act

-- #check the harness on this step function.
#check (iterateUntilFix (k := 2) (f := step) (a := S))

end Generative
end Tests
end HeytingLean

