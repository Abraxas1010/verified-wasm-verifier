import HeytingLean.Coalgebra.Universal.Bisimulation

/-!
# Universal coalgebra (Type) — coinduction lemma suite

This file re-exports the relation-based bisimulation interface and provides a
convenient coinduction theorem name.

For concrete coinductive objects (e.g. streams), Mathlib often already provides a
specialized coinduction principle; see `Mathlib.Data.Stream.Init`.
-/

namespace HeytingLean
namespace Coalgebra
namespace Universal

universe u

open CategoryTheory
open RelBisim

variable {F : Type u ⥤ Type u} [Relator F]

/-- Coinduction: to prove bisimilarity, it suffices to exhibit a bisimulation relation. -/
theorem coinduction {S T : Universal.Coalg (F := F)} {R : Rel S.V T.V}
    (hR : IsBisimulation (F := F) S T R) :
    R ≤ᵣ Bisimilar (F := F) S T :=
  RelBisim.coinduction (F := F) hR

end Universal
end Coalgebra
end HeytingLean
