import HeytingLean.EpistemicCalculus.Basic
import HeytingLean.EpistemicCalculus.Axioms
import HeytingLean.Core.Heyting.Basic
import HeytingLean.Logic.ResiduatedCore

namespace HeytingLean.EpistemicCalculus

/-- Fixed points of a Heyting nucleus. -/
abbrev NucleusFixedPt {α : Type*} [_root_.HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α) : Type _ :=
  { x : α // N.op x = x }

@[ext] theorem NucleusFixedPt.ext {α : Type*} [_root_.HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α)
    {x y : NucleusFixedPt N} (h : (x : α) = (y : α)) : x = y := by
  exact Subtype.ext (by simpa using h)

def nucleusFusion {α : Type*} [_root_.HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α)
    (x y : NucleusFixedPt N) : NucleusFixedPt N :=
  ⟨x.1 ⊓ y.1, by
    calc
      N.op (x.1 ⊓ y.1) = N.op x.1 ⊓ N.op y.1 := N.preserves_meet x.1 y.1
      _ = x.1 ⊓ y.1 := by simp [x.2, y.2]⟩

def nucleusUnit {α : Type*} [_root_.HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α) : NucleusFixedPt N :=
  ⟨⊤, by
    apply le_antisymm
    · exact le_top
    · exact N.extensive ⊤⟩

/-- Fold a list of nucleus fixed points using meet in the ambient carrier. -/
def fusedTrustValue {α : Type*} [_root_.HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α)
    (values : List (NucleusFixedPt (α := α) N)) : α :=
  values.foldl (fun (acc : α) (value : NucleusFixedPt N) => acc ⊓ (value : α)) ⊤

/-- If the accumulator is already fixed, folding in more fixed points stays fixed. -/
theorem nucleus_foldl_meet_fixed
    {α : Type*} [_root_.HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α)
    (acc : α) (values : List (NucleusFixedPt N))
    (hacc : N.op acc = acc) :
    N.op (values.foldl (fun (x : α) (value : NucleusFixedPt N) => x ⊓ (value : α)) acc) =
      values.foldl (fun (x : α) (value : NucleusFixedPt N) => x ⊓ (value : α)) acc := by
  induction values generalizing acc with
  | nil =>
      simpa using hacc
  | cons value tail ih =>
      simp only [List.foldl_cons]
      refine ih (acc := acc ⊓ (value : α)) ?_
      rw [N.preserves_meet, hacc, value.2]

/-- `EpistemicTrust.combine` cannot fall below the nucleus floor because the fold stays fixed. -/
theorem nucleus_combine_floor_bound
    {α : Type*} [_root_.HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α)
    (values : List (NucleusFixedPt N)) :
    N.op (fusedTrustValue N values) = fusedTrustValue N values := by
  simpa [fusedTrustValue] using
    nucleus_foldl_meet_fixed N ⊤ values (nucleusUnit N).2

/--
The fixed-point locus of a nucleus carries an epistemic calculus with fusion `⊓`
and unit `⊤`.
-/
instance nucleusEpistemicCalculus {α : Type*} [_root_.HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α)
    [hnt : Fact (∃ x y : α, N.op x ≠ N.op y)] :
    EpistemicCalculus (NucleusFixedPt N) where
  fusion := nucleusFusion N
  unit := nucleusUnit N
  fusion_assoc := by
    intro x y z
    apply NucleusFixedPt.ext N
    exact inf_assoc x.1 y.1 z.1
  fusion_comm := by
    intro x y
    apply NucleusFixedPt.ext N
    exact inf_comm x.1 y.1
  fusion_unit_left := by
    intro x
    apply NucleusFixedPt.ext N
    simp [nucleusFusion, nucleusUnit]
  fusion_mono := by
    intro x x' y y' hx hy
    exact inf_le_inf hx hy
  nontrivial := by
    rcases hnt.out with ⟨x, y, hxy⟩
    refine ⟨⟨N.op x, N.idempotent x⟩, ⟨N.op y, N.idempotent y⟩, ?_⟩
    intro h
    exact hxy (congrArg Subtype.val h)
  toPartialOrder := inferInstance

/--
Closedness on fixed points, assuming implication is stable under the nucleus.
This keeps the internal hom on the fixed-point carrier and preserves the Heyting
adjunction.
-/
instance nucleusClosed {α : Type*} [_root_.HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α)
    [Fact (∃ x y : α, N.op x ≠ N.op y)]
    (hhimp_closed : ∀ a b : α, N.op (a ⇨ b) = (a ⇨ b)) :
    Closed (NucleusFixedPt N) where
  ihom := fun y z => ⟨N.op (y.1 ⇨ z.1), N.idempotent (y.1 ⇨ z.1)⟩
  adjunction := by
    intro x y z
    constructor
    · intro hxy
      have hxy' : x.1 ⊓ y.1 ≤ z.1 := by
        simpa [nucleusFusion] using hxy
      have hx : x.1 ≤ y.1 ⇨ z.1 := (le_himp_iff).2 hxy'
      change x.1 ≤ N.op (y.1 ⇨ z.1)
      simpa [hhimp_closed y.1 z.1] using hx
    · intro hx
      have hx' : x.1 ≤ y.1 ⇨ z.1 := by
        change x.1 ≤ N.op (y.1 ⇨ z.1) at hx
        simpa [hhimp_closed y.1 z.1] using hx
      have hxy' : x.1 ⊓ y.1 ≤ z.1 := (le_himp_iff).1 hx'
      simpa [nucleusFusion] using hxy'

instance nucleusOptimistic {α : Type*} [_root_.HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α)
    [Fact (∃ x y : α, N.op x ≠ N.op y)] :
    Optimistic (NucleusFixedPt N) where
  top := nucleusUnit N
  le_top := by
    intro x
    exact le_top

instance nucleusIdempotent {α : Type*} [_root_.HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α)
    [Fact (∃ x y : α, N.op x ≠ N.op y)] :
    IdempotentFusion (NucleusFixedPt N) where
  idem := by
    intro x
    apply NucleusFixedPt.ext N
    exact inf_idem (a := x.1)

end HeytingLean.EpistemicCalculus
