import HeytingLean.ATheory.Paper.AssemblyIndex
import Mathlib.Data.Nat.Log

namespace HeytingLean
namespace ATheory

namespace Obj

universe u
variable {α : Type u}

/-- The size of a syntax object: number of primitive leaves in the tree. -/
def size : Obj α → Nat
  | Obj.base _ => 1
  | Obj.join l r => size l + size r

@[simp] lemma size_base (a : α) : size (Obj.base a) = 1 := rfl

@[simp] lemma size_join (l r : Obj α) : size (Obj.join l r) = size l + size r := rfl

lemma size_pos (o : Obj α) : 0 < size o := by
  induction o with
  | base a => simp
  | join l r ihl ihr =>
      simpa [size] using Nat.add_pos_left ihl (size r)

lemma size_eq_joinCount_add_one (o : Obj α) : size o = Obj.joinCount o + 1 := by
  induction o with
  | base a => simp [size, Obj.joinCount]
  | join l r ihl ihr =>
      calc
        size (Obj.join l r) = size l + size r := by simp [size]
        _ = (Obj.joinCount l + 1) + (Obj.joinCount r + 1) := by simp [ihl, ihr]
        _ = (Obj.joinCount l + Obj.joinCount r + 1) + 1 := by
            simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = Obj.joinCount (Obj.join l r) + 1 := by simp [Obj.joinCount, Nat.add_assoc]

end Obj

end ATheory

namespace ATheory
namespace Paper

/-!
# Extension 4: Computable bounds on assembly index

We provide trivially-provable lower and upper bounds on the paper-style assembly index.
These are intended as "safe" bounds for approximation / pruning routines; they do not
formalize deep addition-chain theory.
-/

namespace AssemblyBounds

open HeytingLean.ATheory
open scoped Classical

universe u
variable {α : Type u}

/-! ## Upper bound: `size - 1` in the syntax space -/

lemma assemblyIndex_le_size_sub_one [DecidableEq α] (o : Obj α) :
    AssemblySpace.AssemblyIndex.assemblyIndex
        (S := ObjSyntax.space (Atom := α))
        (hC := ObjSyntax.space.closed (Atom := α)) o
      ≤ Obj.size o - 1 := by
  have hle :
      AssemblySpace.AssemblyIndex.assemblyIndex
          (S := ObjSyntax.space (Atom := α))
          (hC := ObjSyntax.space.closed (Atom := α)) o
        ≤ Obj.joinCount o :=
    ObjSyntax.space.assemblyIndex_le_joinCount (Atom := α) (o := o)
  have hs : Obj.size o = Obj.joinCount o + 1 := Obj.size_eq_joinCount_add_one (α := α) o
  have hsub : Obj.joinCount o = Obj.size o - 1 := by
    have : Obj.size o - 1 = Obj.joinCount o := by
      simp [hs]
    exact this.symm
  simpa [hsub] using hle

/-! ## Lower bound: `log₂(size)` in the syntax space -/

namespace ObjSyntax

open Paper.AssemblySpace

private lemma size_le_mul_pow_two_availableAfter
    (A : Set (Obj α)) (M : Nat) :
    ∀ (steps : List (Step (ObjSyntax.space (Atom := α)))),
      (∀ t, t ∈ A → Obj.size t ≤ M) →
      WellFormedFrom (S := ObjSyntax.space (Atom := α)) A steps →
      ∀ t, t ∈ availableAfter (S := ObjSyntax.space (Atom := α)) A steps →
        Obj.size t ≤ M * 2 ^ steps.length := by
  intro steps
  induction steps generalizing A M with
  | nil =>
      intro hA _ t ht
      have ht' : t ∈ A := by
        simpa [availableAfter] using ht
      simpa [availableAfter] using hA t ht'
  | cons s ss ih =>
      intro hA hWF t ht
      rcases hWF with ⟨hsUse, hWF'⟩
      have hx : Obj.size s.x ≤ M := hA s.x hsUse.1
      have hy : Obj.size s.y ≤ M := hA s.y hsUse.2
      have hz : Obj.size s.z ≤ 2 * M := by
        have hTwo : 2 * M = M + M := by
          simp [Nat.succ_mul]
        have hxy : Obj.size s.x + Obj.size s.y ≤ M + M := Nat.add_le_add hx hy
        have hxy' : Obj.size s.z ≤ M + M := by
          -- Rewrite the goal to the unfolded form `Obj.size s.x + Obj.size s.y ≤ M + M`.
          -- Then it is exactly `hxy`.
          rw [s.ok]
          simpa [Obj.size] using hxy
        simpa [hTwo] using hxy'
      have hA' : ∀ t, t ∈ Set.insert s.z A → Obj.size t ≤ 2 * M := by
        intro u hu
        rcases hu with rfl | hu
        · exact hz
        ·
          have : Obj.size u ≤ M := hA u hu
          exact le_trans this (Nat.le_mul_of_pos_left M Nat.zero_lt_two)
      have ht' : t ∈ availableAfter (S := ObjSyntax.space (Atom := α)) (Set.insert s.z A) ss := by
        simpa [availableAfter] using ht
      have ih' := ih (A := Set.insert s.z A) (M := 2 * M) hA' hWF' t ht'
      -- `2 * M * 2^|ss| = M * 2^(|s::ss|)`.
      simpa [List.length, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ih'

private lemma size_le_pow_two_availableAfterU :
    ∀ (steps : List (Step (ObjSyntax.space (Atom := α)))),
      WellFormedFrom (S := ObjSyntax.space (Atom := α)) (ObjSyntax.space (Atom := α)).U steps →
      ∀ t, t ∈ availableAfter (S := ObjSyntax.space (Atom := α)) (ObjSyntax.space (Atom := α)).U steps →
        Obj.size t ≤ 2 ^ steps.length := by
  intro steps hWF t ht
  have hU : ∀ x, x ∈ (ObjSyntax.space (Atom := α)).U → Obj.size x ≤ 1 := by
    intro x hx
    rcases hx with ⟨a, rfl⟩
    simp [Obj.size]
  have := size_le_mul_pow_two_availableAfter (α := α) (A := (ObjSyntax.space (Atom := α)).U)
    (M := 1) steps hU hWF t ht
  simpa using this

end ObjSyntax

lemma assemblyIndex_ge_log2 [DecidableEq α] (o : Obj α) (ho : Obj.size o > 1) :
    Nat.log 2 (Obj.size o)
      ≤
      AssemblySpace.AssemblyIndex.assemblyIndex
        (S := ObjSyntax.space (Atom := α))
        (hC := ObjSyntax.space.closed (Atom := α)) o := by
  -- Choose the minimal-length assembly path (exists by closure).
  rcases AssemblySpace.AssemblyIndex.assemblyIndex_spec
      (S := ObjSyntax.space (Atom := α))
      (hC := ObjSyntax.space.closed (Atom := α)) o with ⟨p, hpLen⟩
  -- Use the nontriviality assumption to rule out the primitive case.
  have _hpNonempty : p.steps ≠ [] := by
    intro hsteps
    rcases p.ok_out with ⟨hsteps', hzU⟩ | hout
    · rcases hzU with ⟨a, rfl⟩
      have : ¬ (Obj.size (Obj.base a) > 1) := by
        simp [HeytingLean.ATheory.Obj.size]
      exact this ho
    · rcases hout with ⟨s, hsLast, _⟩
      simp [hsteps] at hsLast
  have hoAvail : o ∈ AssemblySpace.availableAfter
      (S := ObjSyntax.space (Atom := α))
      (ObjSyntax.space (Atom := α)).U p.steps :=
    AssemblySpace.AssemblyPath.mem_availableAfter (S := ObjSyntax.space (Atom := α)) (z := o) p
  have hsize : Obj.size o ≤ 2 ^ p.len := by
    -- `p.len` is `p.steps.length`.
    have : Obj.size o ≤ 2 ^ p.steps.length :=
      ObjSyntax.size_le_pow_two_availableAfterU (α := α) p.steps p.wf o hoAvail
    simpa [AssemblySpace.AssemblyPath.len] using this
  have hlog' : Nat.log 2 (Obj.size o) ≤ Nat.log 2 (2 ^ p.len) :=
    Nat.log_mono_right hsize
  have hlog : Nat.log 2 (Obj.size o) ≤ p.len := by
    simpa [Nat.log_pow Nat.one_lt_two] using hlog'
  -- Rewrite `p.len` as the assembly index.
  simpa [hpLen] using hlog

/-! ## Bounds for `dagJoinCount` via the syntax-space equality -/

lemma dagJoinCount_bounds [DecidableEq α] (o : Obj α) (ho : Obj.size o > 1) :
    Nat.log 2 (Obj.size o) ≤ Obj.dagJoinCount o ∧ Obj.dagJoinCount o ≤ Obj.size o - 1 := by
  have hlog :
      Nat.log 2 (Obj.size o)
        ≤
        AssemblySpace.AssemblyIndex.assemblyIndex
          (S := ObjSyntax.space (Atom := α))
          (hC := ObjSyntax.space.closed (Atom := α)) o :=
    assemblyIndex_ge_log2 (α := α) o ho
  have hlog' : Nat.log 2 (Obj.size o) ≤ Obj.dagJoinCount o := by
    simpa [ObjSyntax.space.assemblyIndex_eq_dagJoinCount (Atom := α) (o := o)] using hlog
  have hupper : Obj.dagJoinCount o ≤ Obj.size o - 1 := by
    have hle : Obj.dagJoinCount o ≤ Obj.joinCount o := Obj.dagJoinCount_le_joinCount (o := o)
    have hs : Obj.size o = Obj.joinCount o + 1 := Obj.size_eq_joinCount_add_one (α := α) o
    have hsub : Obj.joinCount o = Obj.size o - 1 := by
      have : Obj.size o - 1 = Obj.joinCount o := by
        simp [hs]
      exact this.symm
    exact le_trans hle (by simp [hsub])
  exact ⟨hlog', hupper⟩

/-! ## Conservative approximation -/

/-- A computable upper bound on assembly index, equal to `Obj.dagJoinCount`.

This is NOT a "greedy" algorithm in the algorithmic sense; it simply computes
the reuse-aware join count of the syntax tree. The name reflects that this
is a conservative (non-tight) approximation. -/
def greedyIndex [DecidableEq α] (o : Obj α) : Nat :=
  Obj.dagJoinCount o

lemma greedyIndex_ge_assemblyIndex [DecidableEq α] (o : Obj α) :
    AssemblySpace.AssemblyIndex.assemblyIndex
        (S := ObjSyntax.space (Atom := α))
        (hC := ObjSyntax.space.closed (Atom := α)) o
      ≤ greedyIndex (α := α) o := by
  simp [greedyIndex, ObjSyntax.space.assemblyIndex_eq_dagJoinCount (Atom := α) (o := o)]

/-! ## Computable API for assembly index -/

/-- Computable assembly index for syntax-tree objects.

Although the abstract `AssemblyIndex.assemblyIndex` is noncomputable (defined via
`Nat.find`), we have proved that in the syntax-tree space it equals `Obj.dagJoinCount`.
This definition provides a fast, evaluable interface. -/
def assemblyIndexCompute [DecidableEq α] (o : Obj α) : Nat :=
  Obj.dagJoinCount o

/-- The computable assembly index equals the abstract one in the syntax-tree space. -/
theorem assemblyIndex_eq_compute [DecidableEq α] (o : Obj α) :
    AssemblySpace.AssemblyIndex.assemblyIndex
        (S := ObjSyntax.space (Atom := α))
        (hC := ObjSyntax.space.closed (Atom := α)) o
      = assemblyIndexCompute (α := α) o := by
  simp [assemblyIndexCompute, ObjSyntax.space.assemblyIndex_eq_dagJoinCount (Atom := α) (o := o)]

end AssemblyBounds

end Paper
end ATheory
end HeytingLean
