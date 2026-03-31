import HeytingLean.Genesis.CoGame

/-!
# Genesis.Void

Phase-1 void object in the graph-based co-game substrate.
-/

namespace HeytingLean.Genesis

open CoGame

abbrev Void : CoGame := CoGame.Void

theorem void_has_no_left_options (n : Void.Node) : n ∉ Void.leftSucc Void.root := by
  exact CoGame.void_left_empty n

theorem void_has_no_right_options (n : Void.Node) : n ∉ Void.rightSucc Void.root := by
  exact CoGame.void_right_empty n

theorem void_self_bisim : CoGame.Bisim Void Void := by
  simpa [Void] using CoGame.void_bisim_self

end HeytingLean.Genesis
