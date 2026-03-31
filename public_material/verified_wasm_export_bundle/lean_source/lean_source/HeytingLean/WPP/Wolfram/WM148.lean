import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import HeytingLean.WPP.Wolfram.RewriteFresh

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Wolfram Physics universe WM148 (rule `{{x,y}} -> {{x,y},{y,z}}`)

This file encodes the rule shown in Wolfram Physics Project section *6.3 Causal Invariance*:

* rule: `{{x, y}} -> {{x, y}, {y, z}}` (one fresh vertex `z`)
* initial condition: `{{{0, 0}}}` (a single self-loop)

We implement it as a `SystemFresh Nat (Fin 2)` and provide a **computable** fresh-vertex
allocator for `Nat` that can be used by executables and cross-check scripts.
-/

namespace WM148

abbrev P : Type := Fin 2
abbrev V : Type := Nat

def rule : RuleFresh P where
  nFresh := 1
  lhs := ([[0, 1]] : List (Expr P))
  rhs := ([[Sum.inl 0, Sum.inl 1], [Sum.inl 1, Sum.inr 0]] :
      List (Expr (Sum P (Fin 1))))

def init : HGraph V :=
  ([[0, 0]] : List (Expr V))

def sys : SystemFresh V P where
  rules := [rule]
  init := init

@[simp] lemma sys_rules_length : sys.rules.length = 1 := by
  simp [sys]

/-! ## Well-formedness -/

lemma rule_wellFormed : RuleFresh.WellFormed rule := by
  intro p _hpRhs
  refine ⟨[0, 1], by simp [rule], ?_⟩
  cases p using Fin.cases with
  | zero => simp
  | succ p =>
      have hp0 : p = 0 := Fin.eq_zero p
      subst hp0
      simp

/-! ## A computable fresh allocator for `Nat` -/

open scoped Classical

/-- A simple deterministic fresh vertex for `Nat`: one more than the maximum forbidden vertex. -/
def freshNat (forbidden : Finset Nat) : Nat :=
  forbidden.sup id + 1

lemma freshNat_not_mem (forbidden : Finset Nat) : freshNat forbidden ∉ forbidden := by
  classical
  intro hmem
  have hle : freshNat forbidden ≤ forbidden.sup id := by
    -- `freshNat forbidden ∈ forbidden` implies `freshNat forbidden ≤ sup`.
    simpa [freshNat] using (Finset.le_sup (f := id) (s := forbidden) hmem)
  -- Contradiction: `sup + 1 ≤ sup`.
  have : forbidden.sup id + 1 ≤ forbidden.sup id := by
    simpa [freshNat] using hle
  exact (Nat.not_succ_le_self (forbidden.sup id)) this

/-- Allocate `n` fresh vertices for `Nat`, deterministically as a consecutive block above the maximum. -/
def allocFreshNat (n : Nat) (forbidden : Finset Nat) : Fin n → Nat :=
  fun i => (forbidden.sup id + 1) + i.1

lemma allocFreshNat_injective (n : Nat) (forbidden : Finset Nat) :
    Function.Injective (allocFreshNat n forbidden) := by
  intro i j hij
  apply Fin.ext
  -- cancel the common prefix
  have : i.1 = j.1 := by
    exact Nat.add_left_cancel hij
  exact this

lemma allocFreshNat_not_mem (n : Nat) (forbidden : Finset Nat) (i : Fin n) :
    allocFreshNat n forbidden i ∉ forbidden := by
  classical
  intro hmem
  have hle : allocFreshNat n forbidden i ≤ forbidden.sup id := by
    simpa using (Finset.le_sup (f := id) (s := forbidden) hmem)
  -- But `sup + 1 ≤ sup` is impossible, even before adding `i`.
  have : forbidden.sup id + 1 ≤ forbidden.sup id := by
    -- `sup + 1 ≤ sup` follows from `sup + 1 + i ≤ sup` by monotonicity.
    have h' : forbidden.sup id + 1 + i.1 ≤ forbidden.sup id := by
      simpa [allocFreshNat, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hle
    exact le_trans (Nat.le_add_right (forbidden.sup id + 1) i.1) h'
  exact (Nat.not_succ_le_self (forbidden.sup id)) this

/-! ## Deterministic step (used by executables) -/

open SystemFresh

variable [DecidableEq V]

/-- The unique rule index (`0`) for `sys`. -/
def idx0 : Fin sys.rules.length :=
  ⟨0, by simp [sys]⟩

/-- Build an event for the unique rule, from a substitution `σ`. -/
def mkEvent (σ : P → V) : sys.Event :=
  { idx := idx0, σ := σ }

/-- Deterministically apply an event, allocating fresh vertices as `allocFreshNat` above `verts s`. -/
def applyDet (e : sys.Event) (s : HGraph V) : HGraph V :=
  e.applyWith (allocFreshNat e.rule.nFresh (HGraph.verts (V := V) s)) s

end WM148

end Wolfram
end WPP
end HeytingLean
