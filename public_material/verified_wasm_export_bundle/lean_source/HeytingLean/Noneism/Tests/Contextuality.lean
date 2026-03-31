import HeytingLean.Noneism.Contextuality.Examples.MagicSquare
import HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerSphere

namespace HeytingLean
namespace Noneism
namespace Tests

open Contextuality
open Contextuality.Examples

example : Contextuality.Contextual MagicSquare.magicSquareScenario :=
  MagicSquare.magicSquare_contextual

example : ¬ ∃ g : MagicSquare.Cell → MagicSquare.Outcome,
    Contextuality.IsGlobalSection MagicSquare.magicSquareScenario g :=
  MagicSquare.magicSquare_no_global_section

example : ¬ Nonempty KochenSpeckerSphere.OneZeroOneFunc :=
  KochenSpeckerSphere.no_noncontextual_global_assignment

end Tests
end Noneism
end HeytingLean
