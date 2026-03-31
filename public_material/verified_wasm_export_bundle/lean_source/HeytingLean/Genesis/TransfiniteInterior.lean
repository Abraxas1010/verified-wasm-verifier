import HeytingLean.Genesis.CantorCutBridge
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Genesis.TransfiniteInterior

Bounded transfinite interior lane (Phase 9):
- Level 0 path space (`EvalPath`)
- Level 1 path-functional space (`EvalPath → Bool`)
- Cardinal step witness and interior transport hooks
-/

namespace HeytingLean.Genesis

open Cardinal

/-- Natural-indexed witness-path tower:
`LevelPaths 0 = EvalPath`, `LevelPaths (n+1) = LevelPaths n -> Bool`. -/
def LevelPaths : Nat → Type
  | 0 => EvalPath
  | n + 1 => LevelPaths n → Bool

@[simp] theorem levelPaths_zero : LevelPaths 0 = EvalPath := rfl

@[simp] theorem levelPaths_succ (n : Nat) :
    LevelPaths (n + 1) = (LevelPaths n → Bool) := rfl

/-- Implemented witness levels for the bounded transfinite lane. -/
inductive WitnessLevel where
  | zero
  | one
  deriving DecidableEq, Repr

/-- Level-0 carrier: Cantor-cut paths. -/
abbrev Level0Paths : Type := LevelPaths 0

/-- Level-1 carrier: predicates on level-0 paths. -/
abbrev Level1Paths : Type := LevelPaths 1

/-- Level-2 carrier: predicates on level-1 predicates. -/
abbrev Level2Paths : Type := LevelPaths 2

/-- Type carrier by implemented witness level. -/
def levelCarrier : WitnessLevel → Type
  | .zero => Level0Paths
  | .one => Level1Paths

/-- Cardinal recurrence across the natural witness tower. -/
theorem levelPaths_card_succ (n : Nat) :
    #(LevelPaths (n + 1)) = 2 ^ #(LevelPaths n) := by
  rw [levelPaths_succ, ← Cardinal.power_def Bool (LevelPaths n), Cardinal.mk_bool]

/-- Cardinality at level 0. -/
theorem level0_paths_cardinality : #Level0Paths = Cardinal.continuum := by
  exact evalPath_card

/-- Cardinality at level 1. -/
theorem level1_paths_cardinality : #Level1Paths = 2 ^ Cardinal.continuum := by
  have h0 : #Level1Paths = 2 ^ #Level0Paths := by
    exact levelPaths_card_succ 0
  calc
    #Level1Paths = 2 ^ #Level0Paths := h0
    _ = 2 ^ Cardinal.continuum := by rw [level0_paths_cardinality]

/-- Level-1 cardinality as a direct jump from the level-0 base. -/
theorem level1_paths_cardinality_step : #Level1Paths = 2 ^ #Level0Paths := by
  calc
    #Level1Paths = 2 ^ Cardinal.continuum := level1_paths_cardinality
    _ = 2 ^ #Level0Paths := by rw [level0_paths_cardinality]

/-- Cardinality at level 2. -/
theorem level2_paths_cardinality : #Level2Paths = 2 ^ #Level1Paths := by
  exact levelPaths_card_succ 1

/-- Strict growth witness from level 0 to level 1. -/
theorem level0_lt_level1 : #Level0Paths < #Level1Paths := by
  have h := Cardinal.cantor (#Level0Paths)
  simpa [level1_paths_cardinality_step] using h

/-- Strict growth witness from level 1 to level 2. -/
theorem level1_lt_level2 : #Level1Paths < #Level2Paths := by
  have h := Cardinal.cantor (#Level1Paths)
  simpa [level2_paths_cardinality] using h

/-- Canonical interior lift at level 0 (depth-1 post-re-entry interior). -/
def level0_to_witnessInterior (p : Level0Paths) : WitnessInterior :=
  cantorCut_to_witnessInterior p 0

/-- Canonical level-1 head-bit probe using the all-false base path. -/
def level1HeadBit (Φ : Level1Paths) : Bool :=
  Φ (fun _ => false)

/-- Canonical interior lift at level 1 via the head-bit probe. -/
def level1_to_witnessInterior (Φ : Level1Paths) : WitnessInterior :=
  cantorCut_to_witnessInterior (fun _ => level1HeadBit Φ) 1

/-- Transport readiness for level-1 interiors follows the head-bit classification. -/
theorem level1_transport_ready (Φ : Level1Paths) :
    eventualStabilizes (level1_to_witnessInterior Φ).source ↔ level1HeadBit Φ = true := by
  simpa [level1_to_witnessInterior, level1HeadBit] using
    (cantorCut_transport_ready (p := fun _ => level1HeadBit Φ) (depth := 1))

end HeytingLean.Genesis
