/-!
# Universal hash families (interface-first)

We keep the definition minimal and finite/combinatorial.
-/

namespace HeytingLean
namespace Crypto
namespace Information
namespace Hashing

universe u v w

/-- A hash family from domain `D` to range `R`, parameterized by a seed `S`. -/
structure HashFamily (D : Type u) (R : Type v) (S : Type w) where
  hash : S → D → R

end Hashing
end Information
end Crypto
end HeytingLean

