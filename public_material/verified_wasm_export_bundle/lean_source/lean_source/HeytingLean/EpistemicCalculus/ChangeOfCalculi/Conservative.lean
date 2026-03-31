import HeytingLean.EpistemicCalculus.Basic

namespace HeytingLean.EpistemicCalculus.ChangeOfCalculi

/--
Conservative change of calculi: monotone and lax monoidal.
Fusion in the target is no stronger than mapped fusion from the source.
-/
structure ConservativeChange (V W : Type*)
    [EpistemicCalculus V] [EpistemicCalculus W] where
  map : V → W
  monotone : ∀ {x y : V}, x ≤ y → map x ≤ map y
  lax_monoidal : ∀ x y : V, map x fus map y ≤ map (x fus y)
  lax_unit : EpistemicCalculus.unit ≤ map EpistemicCalculus.unit

end HeytingLean.EpistemicCalculus.ChangeOfCalculi
