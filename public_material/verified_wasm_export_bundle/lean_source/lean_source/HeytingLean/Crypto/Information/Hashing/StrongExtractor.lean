import HeytingLean.Crypto.Information.Hashing.UniversalHash

/-!
# Strong extractors (interface-first)

We treat an extractor as a family of functions `S → D → R` with a security statement packaged
externally (e.g. via the Leftover Hash Lemma interface).
-/

namespace HeytingLean
namespace Crypto
namespace Information
namespace Hashing

universe u v w

/-- A strong extractor (function family). -/
structure StrongExtractor (D : Type u) (R : Type v) (S : Type w) where
  extract : S → D → R

end Hashing
end Information
end Crypto
end HeytingLean

