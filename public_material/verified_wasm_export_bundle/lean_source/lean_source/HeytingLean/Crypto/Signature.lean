import HeytingLean.Crypto.Signature.Spec

/-
# Crypto.Signature

Facade module re-exporting the abstract signature specification layer.
Concrete schemes can be added under `HeytingLean.Crypto.Signature`
and are expected to instantiate the interfaces from `Signature.Spec`.
-/

namespace HeytingLean
namespace Crypto
namespace Signature

-- For now we simply re-export the `Spec` namespace.

end Signature
end Crypto
end HeytingLean

