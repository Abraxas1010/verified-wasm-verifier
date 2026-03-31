import CombinatorialGames.Game.IGame
import HeytingLean.Numbers.SurrealCore

/-!
# Bridge: `SurrealCore.PreGame` → CGT `IGame`

This module provides an explicit interoperability bridge from the repo’s lightweight,
finite `SurrealCore.PreGame` representation (lists of left/right options) to Mathlib’s
pre-game type, which has been migrated out of Mathlib into the CGT repository as `IGame`.

The bridge is conceptually:

`{L | R}` (our `PreGame`) ↦ `!{range (map toIGame L) | range (map toIGame R)}` (CGT `IGame`).

This is the “explicit bridge” requested for connecting the `{L | R}` distinction story
to an existing verified formalization.

Semantic mapping (project doctrine):
- This bridge is intentionally `noncomputable` because the CGT `IGame` constructor uses sets/ranges,
  which is naturally non-executable.
- This is treated as a **semantic-closure crossing marker** (“existence/structure → selected witness”),
  not as “extra power”.
- For an executable bridge, see `HeytingLean.Numbers.Surreal.BridgeToFGame` (`PreGame.toFGame`).
- See `Docs/Semantics.md` for the repo-wide “find the crossing” workflow.
-/

namespace HeytingLean
namespace Numbers
namespace SurrealCore

namespace PreGame

private theorem sizeOf_lt_sizeOf_list_of_mem [SizeOf α] {x : α} {xs : List α} (hx : x ∈ xs) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil => cases hx
  | cons h t ih =>
      cases hx with
      | head =>
          have hpos : 0 < 1 + sizeOf t := by
            have : 0 < sizeOf t + 1 := Nat.succ_pos _
            refine lt_of_lt_of_eq this ?_
            simp [Nat.add_comm]
          have hlt : sizeOf x < sizeOf x + (1 + sizeOf t) :=
            Nat.lt_add_of_pos_right hpos
          refine lt_of_lt_of_eq hlt ?_
          rw [List.cons.sizeOf_spec]
          calc
            sizeOf x + (1 + sizeOf t) = 1 + (sizeOf x + sizeOf t) := by
              exact Nat.add_left_comm (sizeOf x) 1 (sizeOf t)
            _ = 1 + sizeOf x + sizeOf t := by
              exact (Eq.symm (Nat.add_assoc 1 (sizeOf x) (sizeOf t)))
      | tail _ hx1 =>
          have hlt : sizeOf x < sizeOf t := ih hx1
          have htpos : 0 < 1 + sizeOf h := by
            have : 0 < sizeOf h + 1 := Nat.succ_pos _
            refine lt_of_lt_of_eq this ?_
            simp [Nat.add_comm]
          have ht_lt : sizeOf t < sizeOf t + (1 + sizeOf h) :=
            Nat.lt_add_of_pos_right htpos
          have ht_lt' : sizeOf t < sizeOf (h :: t) := by
            refine lt_of_lt_of_eq ht_lt ?_
            rw [List.cons.sizeOf_spec]
            calc
              sizeOf t + (1 + sizeOf h) = 1 + (sizeOf t + sizeOf h) := by
                exact Nat.add_left_comm (sizeOf t) 1 (sizeOf h)
              _ = 1 + sizeOf t + sizeOf h := by
                exact (Eq.symm (Nat.add_assoc 1 (sizeOf t) (sizeOf h)))
              _ = 1 + sizeOf h + sizeOf t := by
                exact Nat.add_right_comm 1 (sizeOf t) (sizeOf h)
          exact Nat.lt_trans hlt ht_lt'

private theorem sizeOf_lt_sizeOf_pregame_mk_left
    (L R : List PreGame) (birth : Nat) {x : PreGame} (hx : x ∈ L) :
    sizeOf x < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
  have hx' : sizeOf x < sizeOf L := sizeOf_lt_sizeOf_list_of_mem hx
  have hpos : 0 < (1 + sizeOf R + sizeOf birth) := by
    refine lt_of_lt_of_eq (Nat.succ_pos (sizeOf R + sizeOf birth)) ?_
    simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
  have hlt : sizeOf L < sizeOf L + (1 + sizeOf R + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hL : sizeOf L < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
    simpa [PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hx' hL

private theorem sizeOf_lt_sizeOf_pregame_mk_right
    (L R : List PreGame) (birth : Nat) {x : PreGame} (hx : x ∈ R) :
    sizeOf x < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
  have hx' : sizeOf x < sizeOf R := sizeOf_lt_sizeOf_list_of_mem hx
  have hpos : 0 < (1 + sizeOf L + sizeOf birth) := by
    refine lt_of_lt_of_eq (Nat.succ_pos (sizeOf L + sizeOf birth)) ?_
    simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
  have hlt : sizeOf R < sizeOf R + (1 + sizeOf L + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hR : sizeOf R < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
    simpa [PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hx' hR

/-- Translate a finite `SurrealCore.PreGame` into CGT’s `IGame`. -/
noncomputable def toIGame : PreGame → IGame
  | { L := L, R := R, birth := _ } =>
      let L' := L.map toIGame
      let R' := R.map toIGame
      let s : Set IGame := Set.range (fun i : Fin L'.length => L'.get i)
      let t : Set IGame := Set.range (fun i : Fin R'.length => R'.get i)
      !{s | t}
termination_by g => sizeOf g
decreasing_by
  all_goals
    first
    | exact sizeOf_lt_sizeOf_pregame_mk_left _ _ _ (by assumption)
    | exact sizeOf_lt_sizeOf_pregame_mk_right _ _ _ (by assumption)

end PreGame

end SurrealCore
end Numbers
end HeytingLean
