import HeytingLean.Bridges.Geo.Examples

namespace HeytingLean
namespace Tests
namespace Geo

open HeytingLean.Bridges.Geo
open HeytingLean.Bridges.Geo.Examples

/-!
Compile-only sanity for the Bool indiscrete Geo example.
We #check the model and exercise the nucleus fields on arbitrary sets.
-/

variable (S T : Set Bool)

-- The example interior-based IntReentry on Set Bool
#check R_geo

-- Deflationary: interior S ⊆ S (via `apply_le` field)
#check R_geo.nucleus.apply_le S

-- Idempotent: interior (interior S) = interior S
#check R_geo.nucleus.idempotent S

-- Meets-preserving: interior (S ∩ T) = interior S ∩ interior T
#check R_geo.nucleus.map_inf S T

-- Assemble a Geo model from R_geo
#check model

end Geo
end Tests
end HeytingLean

