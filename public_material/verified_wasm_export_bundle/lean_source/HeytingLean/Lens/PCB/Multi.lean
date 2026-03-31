import HeytingLean.Logic.Booleanization
import HeytingLean.Probability

/-!
Proof-Carrying Boolean (PCB) Lens — Multi-branch flavor.
Represents a finite distribution over high-level states and a Booleanized
distribution view, with a policy for lifting Boolean posteriors.
-/

namespace HeytingLean
namespace Lens
namespace PCB

open HeytingLean.Logic
open HeytingLean.Probability

universe u

variable {Ω : Type u} [Inhabited Ω] [DecidableEq Ω]

structure MultiUpdatePolicy (Ω : Type u) [Inhabited Ω] [DecidableEq Ω] where
  lift : Dist (Reg Ω) → Dist Ω

structure MultiState (Ω : Type u) [Inhabited Ω] [DecidableEq Ω] where
  hiDist : Dist Ω
  loDist : Dist (Reg Ω)

namespace MultiState

noncomputable def fromHiDist (d : Dist Ω) : MultiState Ω :=
  { hiDist := d, loDist := Dist.mapCoalesce (toBool) d 0 }

def get (s : MultiState Ω) : Dist (Reg Ω) := s.loDist

noncomputable def update (policy : MultiUpdatePolicy Ω)
  (_s : MultiState Ω) (b' : Dist (Reg Ω)) : MultiState Ω :=
  let hi' := policy.lift b'
  { hiDist := hi', loDist := b' }

end MultiState

/-! Build a MultiUpdatePolicy from a lifting function. -/
noncomputable def liftFrom (lift : Reg Ω → Ω)
  [Inhabited Ω] [DecidableEq Ω] : MultiUpdatePolicy Ω :=
  { lift := fun d => Dist.mapCoalesce lift d 0 }

/-!
Score‑based lifting: push `Dist (Reg Ω)` forward via `lift` and
reweight by a (nonnegative) `score : Ω → ℝ`, then renormalize.
This is useful when the Boolean posterior carries a quality metric
for reconstructed high-level states.
-/
noncomputable def liftScoreFrom (lift : Reg Ω → Ω) (score : Ω → ℝ)
  [Inhabited Ω] [DecidableEq Ω] : MultiUpdatePolicy Ω :=
  { lift := fun d =>
      let idxs := List.range d.support.size
      let pairs : List (Ω × ℝ) := idxs.map (fun i =>
        let b  := d.support[i]!
        let w  := d.weights.get! i
        let o  := lift b
        let s  := max 0 (score o)
        (o, w * s))
      let arr : Array (Ω × ℝ) := pairs.toArray
      Dist.fromPairs arr |> Dist.canonicalize (trimTol := 0) }

end PCB
end Lens
end HeytingLean
