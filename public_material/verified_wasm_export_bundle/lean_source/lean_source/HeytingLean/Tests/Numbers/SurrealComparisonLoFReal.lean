import HeytingLean.Numbers.Surreal.ComparisonLoF

open Classical

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore

-- Galois connection typechecks for the default instance
example :
  GaloisConnection
    (HeytingLean.Numbers.Surreal.f_lof)
    (HeytingLean.Numbers.Surreal.g_lof) :=
  HeytingLean.Numbers.Surreal.gc_lof

-- Factor well-typed and diamond commutes pointwise
example (S : Set PreGame) :
  HeytingLean.Numbers.Surreal.f_lof S ≤
  HeytingLean.Numbers.Surreal.factor_lof
    ⟨ (HeytingLean.Numbers.Surreal.R_comp_lof).act S,
      (HeytingLean.Numbers.Surreal.R_comp_lof).idempotent S ⟩ :=
  HeytingLean.Numbers.Surreal.diamond_commutes_pointwise_le (S := S)

end Numbers
end Tests
end HeytingLean
