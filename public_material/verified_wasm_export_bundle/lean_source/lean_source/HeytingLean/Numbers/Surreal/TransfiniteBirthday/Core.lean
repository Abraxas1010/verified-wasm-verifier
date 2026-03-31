import HeytingLean.Numbers.Surreal.TransfinitePreGame
import HeytingLean.Numbers.Ordinal.Notation

/-!
# Transfinite birthday negation invariance (nat fragment)

Defines a syntactic `negOptionSet`/`negPreGame` operation on transfinite
pre-games (swaps left ↔ right), then proves that birthday is invariant
under this operation **for the `PreGame.nat n` family only**.

Scope limitation: `negOptionSet` maps infinite option-set constructors
(`.nats`, `.omegaPlusNats`, `.omegaTimesTwoPlusNats`) to themselves.
This is NOT correct negation for those families (e.g., negating
`{0,1,2,...}` should yield `{0,−1,−2,...}`), but the function must be
total for the mutual definition to compile. The identity fallback is
never exercised by `PreGame.nat`, which uses only `.finite`.

A general `birth_negPreGame` theorem covering arbitrary finite-tree
games (not just the `nat` subfamily) would require structural induction
on mutual inductives, which Lean 4 does not yet support via the
`induction` tactic on mutual types.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace TransfiniteBirthday

open HeytingLean.Numbers.Ordinal
open HeytingLean.Numbers.Surreal.TransfinitePreGame

mutual
  def negOptionSet : OptionSet → OptionSet
    | .finite xs => .finite (xs.map negPreGame)
    | .nats => .nats
    | .omegaPlusNats => .omegaPlusNats
    | .omegaTimesTwoPlusNats => .omegaTimesTwoPlusNats
    | .union a b => .union (negOptionSet a) (negOptionSet b)

  def negPreGame : PreGame → PreGame
    | .cut L R => .cut (negOptionSet R) (negOptionSet L)
end

@[simp] theorem negOptionSet_finite (xs : List PreGame) :
    negOptionSet (.finite xs) = .finite (xs.map negPreGame) := by
  simp [negOptionSet]

@[simp] theorem negOptionSet_union (a b : OptionSet) :
    negOptionSet (.union a b) = .union (negOptionSet a) (negOptionSet b) := by
  simp [negOptionSet]

@[simp] theorem negPreGame_cut (L R : OptionSet) :
    negPreGame (.cut L R) = .cut (negOptionSet R) (negOptionSet L) := by
  simp [negPreGame]

/-- Birthday of PreGame.nat n is invariant under negation. -/
theorem birth_negPreGame_nat : ∀ n,
    birth (negPreGame (PreGame.nat n)) = birth (PreGame.nat n)
  | 0 => by
      simp [PreGame.nat, PreGame.zero]
  | n + 1 => by
      simp only [PreGame.nat]
      simp only [negPreGame_cut, negOptionSet_finite, List.map, birth, supSucc,
        OrdinalCNF.supList]
      rw [birth_negPreGame_nat n]
      exact OrdinalCNF.max_comm _ _

end TransfiniteBirthday
end Surreal
end Numbers
end HeytingLean
