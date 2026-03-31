import HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.ContextualityBridge

/-!
# Contextuality support cardinalities (triangle demo)

Thin re-export layer for the small “support size” facts about the triangle contextuality witness.
-/

namespace HeytingLean
namespace Quantum
namespace Contextuality
namespace Triangle
namespace Cardinality

open HeytingLean.LoF.CryptoSheaf.Quantum

abbrev supportAB_size_two :=
  HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.supportAB_size_two

abbrev supportBC_size_two :=
  HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.supportBC_size_two

end Cardinality
end Triangle
end Contextuality
end Quantum
end HeytingLean
