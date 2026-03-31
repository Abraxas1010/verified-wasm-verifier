namespace HeytingLean.Core

universe u v

/--
A witness step consumes an upstream witness value. Requiring an explicit
`upstream` projection makes witness threading inspectable and reusable.
-/
class IsWitnessStep (W : Type u) where
  Upstream : Type v
  upstream : W -> Upstream

/-- Convenience alias for the upstream witness type of a step. -/
abbrev UpstreamOf (W : Type u) [IsWitnessStep W] : Type _ :=
  IsWitnessStep.Upstream (W := W)

/--
A chain root has no upstream witness dependency. `rootEvidence` records the
local property carried by the root witness.
-/
class IsChainRoot (W : Type u) where
  rootEvidence : W -> Prop

/-- Every witness step contains a concrete upstream witness value. -/
theorem upstream_exists
    {W : Type u} [IsWitnessStep W] (w : W) :
    exists u : UpstreamOf W, IsWitnessStep.upstream w = u :=
  Exists.intro (IsWitnessStep.upstream w) rfl

/-- Extract the upstream witness of the upstream witness in a two-step chain. -/
def upstream2
    {W : Type u} [step : IsWitnessStep W] [IsWitnessStep step.Upstream]
    (w : W) : IsWitnessStep.Upstream (W := step.Upstream) :=
  IsWitnessStep.upstream (IsWitnessStep.upstream w)

/-- Any two-step witness exposes its root witness through repeated projection. -/
theorem upstream2_exists
    {W : Type u} [step : IsWitnessStep W] [IsWitnessStep step.Upstream]
    (w : W) :
    exists u : IsWitnessStep.Upstream (W := step.Upstream), upstream2 w = u :=
  Exists.intro (upstream2 w) rfl

end HeytingLean.Core
