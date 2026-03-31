import HeytingLean.Numbers.Surreal.ComparisonLoF

open Classical

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore

-- 1) Galois connection typechecks
example :
  GaloisConnection
    (HeytingLean.Numbers.Surreal.f_lof)
    (HeytingLean.Numbers.Surreal.g_lof) :=
  HeytingLean.Numbers.Surreal.gc_lof

-- 2) Comparison core is a closure core (acts on sets)
example :
  (HeytingLean.Numbers.Surreal.R_comp_lof).act ({} : Set PreGame) =
    (HeytingLean.Numbers.Surreal.R_comp_lof).act ({} : Set PreGame) := rfl

-- 3) Factor is well-typed
example :
  HeytingLean.Numbers.Surreal.Ω_comp_lof → HeytingLean.Numbers.Surreal.Ω_ℓ_lof :=
  HeytingLean.Numbers.Surreal.factor_lof

-- 4) Diamond commutes pointwise by construction
example (S : Set PreGame) :
  HeytingLean.Numbers.Surreal.f_lof S ≤
  HeytingLean.Numbers.Surreal.factor_lof
    ⟨ (HeytingLean.Numbers.Surreal.R_comp_lof).act S,
      (HeytingLean.Numbers.Surreal.R_comp_lof).idempotent S ⟩ :=
  HeytingLean.Numbers.Surreal.diamond_commutes_pointwise_le (S := S)

end Numbers
end Tests
end HeytingLean
