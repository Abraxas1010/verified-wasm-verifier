import HeytingLean.Chem.PeriodicTable.CovalentRadii
import HeytingLean.Chem.PeriodicTable.Elements

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem.PeriodicTable
open HeytingLean.Chem.PeriodicTable.Elements

-- Compile-only sanity checks: confirms the frozen table is wired to our Element model.
example : covalentRadiusAngstrom? H = some (310 / 1000 : ℚ) := rfl
example : covalentRadiusAngstrom? O = some (660 / 1000 : ℚ) := rfl
example : covalentRadiusAngstrom? Fe = some (1320 / 1000 : ℚ) := rfl

end Tests
end Chem
end HeytingLean

