import HeytingLean.Logic.Booleanization
import Mathlib.Data.Real.Basic
import HeytingLean.Lens.PCB.Single

/-!
Distance/Score scaffolding for PCB lens policies.
- `makeSinglePolicy`: build a policy from a retraction `lift : Reg Ω → Ω` with left/right inverse proofs.
- Typeclasses `Distance` and `Score` for future minimal-change or free-energy selection.
-/

namespace HeytingLean
namespace Lens
namespace PCB

open HeytingLean.Logic

universe u

class Distance (Ω : Type u) where
  dist : Ω → Ω → Real

class Score (Ω : Type u) where
  score : Ω → Real

noncomputable def chooseArgmin {α} [Inhabited α]
  (xs : Array α) (cost : α → Real) : Option (Nat × α × Real) :=
  if xs.size = 0 then none else
    let initI := 0
    let initA := xs[0]!
    let initC := cost initA
    let rec loop (i : Nat) (bestI : Nat) (bestA : α) (bestC : Real) : Nat × α × Real :=
      if i ≥ xs.size then (bestI, bestA, bestC) else
        let a := xs[i]!
        let c := cost a
        if c < bestC then loop (i+1) i a c else loop (i+1) bestI bestA bestC
    some (loop 1 initI initA initC)

def makeSinglePolicy {Ω : Type u}
  (lift : Reg Ω → Ω)
  (leftInv  : ∀ h : Ω, lift (toBool h) = h)
  (rightInv : ∀ b : Reg Ω, toBool (lift b) = b) :
  SingleUpdatePolicy Ω :=
  { put := fun _ b => lift b
  , put_get_id := by intro h; simpa using leftInv h
  , view_consistency := by intro h b'; simpa using rightInv b' }

/-!
Build a law-abiding policy from a candidate generator:
  - `cands : Reg Ω → Array Ω` lists admissible high-level states for a Boolean view.
  - `mem_toBool` ensures `h` is in candidates of `toBool h` so `put_get_id` holds.
  - `sound` ensures all candidates project back to the Boolean view, so `view_consistency` holds.
  - `cost : Reg Ω → Ω → ℝ` ranks candidates; the argmin is chosen.
-/
-- Note: A candidate-based policy can be assembled by providing a retraction `lift`
-- with left/right inverse proofs and (optionally) selecting `lift` via `chooseArgmin`.

end PCB
end Lens
end HeytingLean
