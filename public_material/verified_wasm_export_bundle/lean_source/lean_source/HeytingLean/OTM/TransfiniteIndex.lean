import HeytingLean.OTM.Assembly
import HeytingLean.Numbers.Ordinal.Notation
import HeytingLean.Numbers.Surreal.TransfinitePreGame

namespace HeytingLean
namespace OTM

open HeytingLean.Numbers

universe u v

/-- OTM-facing transfinite index carrier (computable CNF notation below `ε₀`). -/
abbrev TransfiniteIndex := Ordinal.OrdinalCNF

/-- Fuel-index embedding into transfinite indices. -/
def fuelIndex (fuel : Nat) : TransfiniteIndex :=
  Ordinal.OrdinalCNF.ofNat fuel

/-- Surreal pre-game birthday embedding into transfinite indices. -/
def preGameIndex (g : Surreal.TransfinitePreGame.PreGame) : TransfiniteIndex :=
  Surreal.TransfinitePreGame.birth g

/-- Pair a fuel-bounded OTM run with its ordinal index witness. -/
def runWithIndex
    {ι : Type u} {α : Type v} [DecidableEq ι] [LoF.PrimaryAlgebra α]
    (fuel : Nat) (M : Machine ι α) : Machine ι α × TransfiniteIndex :=
  (Machine.run fuel M, fuelIndex fuel)

@[simp] theorem runWithIndex_fst
    {ι : Type u} {α : Type v} [DecidableEq ι] [LoF.PrimaryAlgebra α]
    (fuel : Nat) (M : Machine ι α) :
    (runWithIndex fuel M).1 = Machine.run fuel M := rfl

@[simp] theorem runWithIndex_snd
    {ι : Type u} {α : Type v} [DecidableEq ι] [LoF.PrimaryAlgebra α]
    (fuel : Nat) (M : Machine ι α) :
    (runWithIndex fuel M).2 = fuelIndex fuel := rfl

/-- Finite natural pre-games embed to the same ordinal index as finite fuel. -/
theorem preGameIndex_nat (n : Nat) :
    preGameIndex (Surreal.TransfinitePreGame.PreGame.nat n) = fuelIndex n := by
  induction n with
  | zero =>
      native_decide
  | succ n ih =>
      calc
        preGameIndex (Surreal.TransfinitePreGame.PreGame.nat (Nat.succ n))
            = Ordinal.OrdinalCNF.succ
                (preGameIndex (Surreal.TransfinitePreGame.PreGame.nat n)) := by
                  simp [preGameIndex]
        _ = Ordinal.OrdinalCNF.succ (fuelIndex n) := by
              simp [ih]
        _ = fuelIndex (Nat.succ n) := by
              change
                Ordinal.OrdinalCNF.ofNat n + Ordinal.OrdinalCNF.ofNat 1 =
                  Ordinal.OrdinalCNF.ofNat (Nat.succ n)
              exact Ordinal.OrdinalCNF.ofNat_add_one_succ n

@[simp] theorem preGameIndex_omega :
    preGameIndex Surreal.TransfinitePreGame.PreGame.omega = Ordinal.OrdinalCNF.omega := by
  simp [preGameIndex]

@[simp] theorem preGameIndex_omegaTimesTwo :
    preGameIndex Surreal.TransfinitePreGame.PreGame.omegaTimesTwo =
      Ordinal.OrdinalCNF.omega + Ordinal.OrdinalCNF.omega := by
  simp [preGameIndex]

/--
Phase-F (P2) packaging theorem:
the transfinite index lane is concretely realized by
1) finite-fuel indices,
2) surreal birthday embeddings, and
3) run-index pairing for OTM executions.
-/
theorem otm_transfinite_index_lane_well_defined
    {ι : Type u} {α : Type v} [DecidableEq ι] [LoF.PrimaryAlgebra α] :
    preGameIndex Surreal.TransfinitePreGame.PreGame.omega = Ordinal.OrdinalCNF.omega ∧
      preGameIndex Surreal.TransfinitePreGame.PreGame.omegaTimesTwo =
        Ordinal.OrdinalCNF.omega + Ordinal.OrdinalCNF.omega ∧
      ∀ fuel (M : Machine ι α), (runWithIndex fuel M).2 = fuelIndex fuel := by
  refine ⟨preGameIndex_omega, preGameIndex_omegaTimesTwo, ?_⟩
  intro fuel M
  rfl

end OTM
end HeytingLean
