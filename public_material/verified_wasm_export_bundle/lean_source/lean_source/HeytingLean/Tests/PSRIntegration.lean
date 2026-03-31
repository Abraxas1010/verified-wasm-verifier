import HeytingLean.Logic.PSR
import HeytingLean.Logic.Dialectic

namespace HeytingLean
namespace Tests
namespace PSRIntegration

open HeytingLean.LoF
open HeytingLean.Logic

universe u

section
variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α)

-- #check core PSR API
#check Logic.PSR.Sufficient (R := R)
#check Logic.PSR.sufficient_stable (R := R)
#check Logic.PSR.minimal_reason_exists (R := R)

-- #check dialectic least property 
variable {a T A W : α}
#check Logic.Dialectic.synthesis_least (R := R)

end

end PSRIntegration
end Tests
end HeytingLean

