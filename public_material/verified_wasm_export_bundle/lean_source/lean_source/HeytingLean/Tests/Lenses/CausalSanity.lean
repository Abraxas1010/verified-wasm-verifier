import HeytingLean.Bridges.Causal

namespace HeytingLean
namespace Tests
namespace Lenses

open Bridges

/-- Compile-only sanity for the Causal lens. -/
def tinyPreds (v : String) : Set String :=
  -- edges: A→B, B→C (i.e., A ∈ preds B, B ∈ preds C)
  if v = "B" then {u | u = "A"}
  else if v = "C" then {u | u = "B"}
  else (∅ : Set String)

def M : Bridges.Causal.Model String := ⟨tinyPreds⟩

-- Check Hull types and basic lemmas are available
#check (Bridges.Causal.Model.Hull (M := M) : Set String → Set String)
#check Bridges.Causal.Model.extensive (M := M)
#check Bridges.Causal.Model.monotone (M := M)
#check Bridges.Causal.Model.idempotent (M := M)

end Lenses
end Tests
end HeytingLean
