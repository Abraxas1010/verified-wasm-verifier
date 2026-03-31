import HeytingLean.EpistemicCalculus.Basic

namespace HeytingLean.EpistemicCalculus.ChangeOfCalculi

/--
Liberal change of calculi: monotone and oplax monoidal.
Mapped fusion is bounded above by fusing mapped values.
-/
structure LiberalChange (V W : Type*)
    [EpistemicCalculus V] [EpistemicCalculus W] where
  map : V → W
  monotone : ∀ {x y : V}, x ≤ y → map x ≤ map y
  oplax_monoidal : ∀ x y : V, map (x fus y) ≤ map x fus map y
  oplax_unit : map EpistemicCalculus.unit ≤ EpistemicCalculus.unit

end HeytingLean.EpistemicCalculus.ChangeOfCalculi
