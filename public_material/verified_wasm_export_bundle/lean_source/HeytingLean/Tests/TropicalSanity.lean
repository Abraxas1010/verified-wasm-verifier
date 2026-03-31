import HeytingLean.Tropical.Differential

/-!
# Tropical sanity

Compile-time checks for the lightweight tropical/ReLU bridge modules.
-/

namespace HeytingLean.Tests.TropicalSanity

#check HeytingLean.Tropical.TropicalReal
#check HeytingLean.Tropical.relu_is_tropical
#check HeytingLean.Tropical.relu_piecewise
#check HeytingLean.Tropical.relu_diff_of_pos
#check HeytingLean.Tropical.relu_diff_of_neg

end HeytingLean.Tests.TropicalSanity

