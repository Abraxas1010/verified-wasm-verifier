import HeytingLean.Crypto.Security.Advantage
import HeytingLean.Crypto.Security.Oracle

namespace HeytingLean
namespace Crypto
namespace Security

/-- Shared reduction surface from one security statement to another. -/
structure Reduction (Source Target : Type) where
  budget : Budget
  transform : Source → Target
  lossUpperBound : Nat

end Security
end Crypto
end HeytingLean
