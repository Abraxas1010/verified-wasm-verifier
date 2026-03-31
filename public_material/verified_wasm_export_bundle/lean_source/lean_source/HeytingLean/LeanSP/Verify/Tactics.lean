import HeytingLean.LeanSP.Verify.Hoare
import HeytingLean.LeanSP.Arith.Word256Props

/-!
# LeanSP.Verify.Tactics

Proof automation: primop dispatch lemmas proved by `rfl`/`unfold`.
These lemmas short-circuit the large match in `evalPurePrimop`.
-/

namespace LeanSP.Verify

open LeanSP.Arith
open LeanSP.EVM

-- ==========================================
-- Primop dispatch lemmas
-- The key insight: evalPurePrimop on a CONCRETE string like "add"
-- reduces by match to the result. We prove this by `unfold` + `rfl`.
-- ==========================================

theorem evalPurePrimop_add (a b : Word256) :
    evalPurePrimop "add" [a, b] = some [add a b] := by
  unfold evalPurePrimop; rfl

theorem evalPurePrimop_sub (a b : Word256) :
    evalPurePrimop "sub" [a, b] = some [sub a b] := by
  unfold evalPurePrimop; rfl

theorem evalPurePrimop_gt (a b : Word256) :
    evalPurePrimop "gt" [a, b] = some [gt a b] := by
  unfold evalPurePrimop; rfl

theorem evalPurePrimop_lt (a b : Word256) :
    evalPurePrimop "lt" [a, b] = some [lt a b] := by
  unfold evalPurePrimop; rfl

-- Lift to evalPrimop (goes through evalPurePrimop first)
@[simp] theorem evalPrimop_add (a b : Word256) (st : YulState) :
    evalPrimop "add" [a, b] st = some ([add a b], st) := by
  unfold evalPrimop; rw [evalPurePrimop_add]

@[simp] theorem evalPrimop_sub (a b : Word256) (st : YulState) :
    evalPrimop "sub" [a, b] st = some ([sub a b], st) := by
  unfold evalPrimop; rw [evalPurePrimop_sub]

@[simp] theorem evalPrimop_gt (a b : Word256) (st : YulState) :
    evalPrimop "gt" [a, b] st = some ([gt a b], st) := by
  unfold evalPrimop; rw [evalPurePrimop_gt]

@[simp] theorem evalPrimop_lt (a b : Word256) (st : YulState) :
    evalPrimop "lt" [a, b] st = some ([lt a b], st) := by
  unfold evalPrimop; rw [evalPurePrimop_lt]

-- ==========================================
-- Block simp lemma
-- ==========================================

@[simp] theorem execSimpleBlock_nil (st : YulState) :
    execSimpleBlock [] st = .ok st := rfl

end LeanSP.Verify
