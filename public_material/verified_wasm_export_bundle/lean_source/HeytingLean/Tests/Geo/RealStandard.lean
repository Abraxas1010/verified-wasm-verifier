import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Intervals.Basic

/-!
Compile-only checks for Real standard topology interiors.
This provides a heavier exemplar demonstrating familiar interiors
of intervals; kept compile-only to avoid runtime costs.
-/

namespace HeytingLean
namespace Tests
namespace Geo

open Set

#check interior (Icc (0 : ℝ) 1)
#check interior (Ici (0 : ℝ))
#check interior (Iic (1 : ℝ))
#check interior (Ioc (0 : ℝ) 1)
#check interior (Ico (0 : ℝ) 1)

-- Where available, mathlib lemmas identify the exact interiors of intervals.
-- We #check the statement names to ensure linkage in this build.
#check interior_Icc
#check interior_Ici
#check interior_Iic

end Geo
end Tests
end HeytingLean

