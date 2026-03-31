import HeytingLean.Bridges.Geo
import HeytingLean.Bridges.Clifford.Commutant

namespace HeytingLean
namespace Tests
namespace Lenses

open HeytingLean.Bridges
open HeytingLean.LoF

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-!
Compile-only sanity checks for lens scaffolds (Geo interior, Clifford commutant).
-/

-- Geo: abstract interior re-entry model
variable (MGeo : Geo.Model (α := α))

#check Geo.Model.Carrier MGeo
#check Geo.Model.contract (M := MGeo)

-- Clifford Commutant: abstract model with IntReentry carrier
variable (MComm : Clifford.Commutant.Model (α := α))

#check Clifford.Commutant.Model.Carrier MComm
#check Clifford.Commutant.Model.contract (M := MComm)

end Lenses
end Tests
end HeytingLean

