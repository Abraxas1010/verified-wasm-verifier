import HeytingLean.LoF.LoFPrimary.Syntax
import HeytingLean.Numbers.SurrealCore

/-!
# Surreal `{L | R}` as a LoF distinction on game-sets

This module is the **Phase 1** “explicit bridge” for the generative stack:

> the surreal pregame constructor `{L | R}` is the Laws-of-Form **distinction**
> (mark/boundary) applied to *game option sets* (left options vs right options).

Implementation note:
* `LoFPrimary` provides only the *syntax* (`void`, `mark`, `juxt`), so the bridge is stated
  at the semantic/data level: a **distinction** is the data of “inside vs outside”.
* A `SurrealCore.PreGame` is exactly such a distinction, on the carrier `List PreGame`,
  with an additional bookkeeping field `birth`.

This file deliberately keeps the bridge structural (and executable) rather than importing
heavy Conway theory. The goal is an explicit, checkable equivalence of **shapes**.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace LoFDerivation

open HeytingLean.LoF
open HeytingLean.Numbers.SurrealCore

/-! ## A generic “distinction” carrier -/

/-- A LoF-style distinction: data of an inside vs outside on some carrier. -/
structure Distinction (α : Type _) where
  inside : α
  outside : α

namespace Distinction

/-- The LoF “mark” as the boundary swap on a distinction carrier. -/
def mark {α : Type _} (d : Distinction α) : Distinction α :=
  ⟨d.outside, d.inside⟩

@[simp] theorem mark_inside {α : Type _} (d : Distinction α) : (mark d).inside = d.outside := rfl
@[simp] theorem mark_outside {α : Type _} (d : Distinction α) : (mark d).outside = d.inside := rfl

end Distinction

/-! ## Game-sets: left vs right options -/

/-- A surreal pregame viewed purely as a distinction of option-sets. -/
abbrev GameDistinction := Distinction (List PreGame)

namespace GameDistinction

/-- Forget the `birth` field: a pregame is (left options, right options). -/
def ofPreGame (g : PreGame) : GameDistinction :=
  ⟨g.L, g.R⟩

/-- Rebuild a pregame from its distinction data, with `birth := 0` (raw `{L|R}` shape). -/
def toPreGameRaw (d : GameDistinction) : PreGame :=
  { L := d.inside, R := d.outside, birth := 0 }

/-- Rebuild a pregame from its distinction data using the canonical `PreGame.build`
(computes a consistent birthday from children). -/
def toPreGame (d : GameDistinction) : PreGame :=
  PreGame.build d.inside d.outside

@[simp] theorem toPreGameRaw_L (d : GameDistinction) : (toPreGameRaw d).L = d.inside := rfl
@[simp] theorem toPreGameRaw_R (d : GameDistinction) : (toPreGameRaw d).R = d.outside := rfl

@[simp] theorem ofPreGame_toPreGameRaw_L (g : PreGame) :
    (toPreGameRaw (ofPreGame g)).L = g.L := by rfl

@[simp] theorem ofPreGame_toPreGameRaw_R (g : PreGame) :
    (toPreGameRaw (ofPreGame g)).R = g.R := by rfl

/-- Round-trip identity on the option-sets: `PreGame` and `GameDistinction` carry the same
left/right data. -/
theorem distinction_pregame_equiv (g : PreGame) :
    (toPreGameRaw (ofPreGame g)).L = g.L ∧ (toPreGameRaw (ofPreGame g)).R = g.R := by
  exact ⟨rfl, rfl⟩

end GameDistinction

/-! ## The “void” distinction and surreal zero -/

namespace SurrealCore.PreGame

/-- Surreal zero as a convenient name for the null cut. -/
abbrev zero : PreGame := SurrealCore.nullCut

end SurrealCore.PreGame

open SurrealCore.PreGame

theorem void_is_zero :
    GameDistinction.toPreGameRaw ({ inside := ([] : List PreGame), outside := ([] : List PreGame) } : GameDistinction)
      = (zero : PreGame) := by
  rfl

/-! ## LoFPrimary syntax tie-in (minimal, semantic) -/

namespace LoFPrimarySemantics

/-- A tiny semantics of LoFPrimary expressions into a distinction carrier.

This is *not* the full boolean semantics; it exists just to document that
the LoF constructor `mark` corresponds to the boundary swap on distinctions. -/
def evalDistinction {α : Type _} [Inhabited α] {n : Nat} :
    HeytingLean.LoF.LoFPrimary.Expr n → (Fin n → Distinction α) → Distinction α
  | .void, _ => ⟨default, default⟩
  | .var i, ρ => ρ i
  | .mark e, ρ => Distinction.mark (evalDistinction e ρ)
  | .juxt e₁ e₂, ρ =>
      let d₁ := evalDistinction e₁ ρ
      let d₂ := evalDistinction e₂ ρ
      ⟨d₁.inside, d₂.outside⟩

@[simp] theorem evalDistinction_mark {α : Type _} {n : Nat}
    [Inhabited α] (e : HeytingLean.LoF.LoFPrimary.Expr n) (ρ : Fin n → Distinction α) :
    evalDistinction (.mark e) ρ = Distinction.mark (evalDistinction e ρ) := rfl

end LoFPrimarySemantics

/-!
### Main bridge statement (data-level)

The repo’s surreal pregame constructor `{L | R}` is literally “a distinction whose inside is `L`
and outside is `R`”, i.e. `GameDistinction.toPreGameRaw ⟨L,R⟩`.
-/

theorem lof_distinction_is_surreal_constructor (L R : List PreGame) :
    GameDistinction.toPreGameRaw ({ inside := L, outside := R } : GameDistinction)
      = ({ L := L, R := R, birth := 0 } : PreGame) := by
  rfl

end LoFDerivation
end Surreal
end Numbers
end HeytingLean
