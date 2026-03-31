/-!
# Pontryagin Duality Signatures (staged)

Lightweight records for LCA groups and characters. No Haar or proofs.
-/

namespace HeytingLean
namespace Analysis
namespace Pontryagin

structure LCA where
  name : String := "staged-LCA"
deriving Repr

structure Character where
  G    : LCA
  note : String := "staged-character"
deriving Repr

end Pontryagin
end Analysis
end HeytingLean

