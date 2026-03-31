import HeytingLean.Noneism.Bridges.CryptoSheaf

/-!
Compile-time smoke check for the CryptoSheaf bridge.
This verifies the bridge definitions remain importable and that the default
witness morphism can be constructed in examples.
-/

namespace HeytingLean
namespace Noneism
namespace Bridge
namespace CryptoSheaf

/-- Smoke witness that the bridge type has at least one constructor. -/
def bridgeSmoke : Nonempty (LoF.CryptoSheaf.ZKMorphism CryptoSheaf.unitSite () ()) :=
  ⟨trivialZK⟩

end CryptoSheaf
end Bridge
end Noneism
end HeytingLean
