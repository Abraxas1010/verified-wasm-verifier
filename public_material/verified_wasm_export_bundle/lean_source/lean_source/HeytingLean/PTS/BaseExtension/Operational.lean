import HeytingLean.PTS.BaseExtension.Syntax

namespace HeytingLean.PTS.BaseExtension

inductive Proves : Program → Goal → Prop where
  | absurd {P : Program} {a : AtomVar} :
      InClosure P Definite.absurd →
      Proves P (.atom a)
  | fact {P : Program} {a : AtomVar} :
      InClosure P (.atom a) →
      Proves P (.atom a)
  | backchain {P : Program} {g : Goal} {a : AtomVar} :
      InClosure P (.imp g a) →
      Proves P g →
      Proves P (.atom a)
  | andI {P : Program} {g₁ g₂ : Goal} :
      Proves P g₁ →
      Proves P g₂ →
      Proves P (.conj g₁ g₂)
  | orL {P : Program} {g₁ g₂ : Goal} :
      Proves P g₁ →
      Proves P (.disj g₁ g₂)
  | orR {P : Program} {g₁ g₂ : Goal} :
      Proves P g₂ →
      Proves P (.disj g₁ g₂)
  | augment {P : Program} {d : Definite} {g : Goal} :
      Proves (d :: P) g →
      Proves P (.imp d g)
  -- NOTE: We hardcode the canonical fresh atom rather than quantifying over every
  -- fresh witness from the paper's generic rule. The missing equivariance lemma
  -- (renaming one fresh witness to another) is deferred; this restricted kernel is
  -- enough for the executable search metatheory because search makes the same choice.
  | generic {P : Program} {g : Goal} :
      Proves P (substGoal g 0 (freshAtomForGoal P g)) →
      Proves P (.all g)
  -- NOTE: As above, the instance rule uses the canonical fresh witness selected by
  -- `freshAtomForAtom`; proving full equivariance is future work.
  | instance_ {P : Program} {d : Definite} {a : Atom} :
      InClosure P (.all d) →
      Proves (substDefinite d 0 (freshAtomForAtom P a) :: P) (.atom (.atom a)) →
      Proves P (.atom (.atom a))

theorem le_maxAtomId_of_mem {atoms : List Atom} {a : Atom} (h : a ∈ atoms) :
    a.id ≤ maxAtomId atoms := by
  induction atoms with
  | nil =>
      cases h
  | cons hd tl ih =>
      simp [maxAtomId] at h ⊢
      cases h with
      | inl hEq =>
          cases hEq
          exact Nat.le_max_left _ _
      | inr htl =>
          exact le_trans (ih htl) (Nat.le_max_right _ _)

theorem freshAtomLiteral_not_mem (atoms : List Atom) :
    ({ id := maxAtomId atoms + 1 } : Atom) ∉ atoms := by
  intro hmem
  have hle : (({ id := maxAtomId atoms + 1 } : Atom)).id ≤ maxAtomId atoms := le_maxAtomId_of_mem hmem
  exact Nat.not_succ_le_self _ (by simpa using hle)

theorem freshAtomForGoal_fresh (P : Program) (g : Goal) :
    FreshForGoal (freshAtomForGoal P g) P g := by
  unfold FreshForGoal freshAtomForGoal
  constructor
  · intro hmem
    exact freshAtomLiteral_not_mem (programAtoms P ++ goalAtoms g)
      (List.mem_append.mpr (Or.inl hmem))
  · intro hmem
    exact freshAtomLiteral_not_mem (programAtoms P ++ goalAtoms g)
      (List.mem_append.mpr (Or.inr hmem))

theorem freshAtomForAtom_fresh (P : Program) (a : Atom) :
    FreshForAtomGoal (freshAtomForAtom P a) a P := by
  unfold FreshForAtomGoal freshAtomForAtom
  constructor
  · intro hEq
    exact freshAtomLiteral_not_mem (programAtoms P ++ [a])
      (List.mem_append.mpr (Or.inr (by simpa using hEq)))
  · intro hmem
    exact freshAtomLiteral_not_mem (programAtoms P ++ [a])
      (List.mem_append.mpr (Or.inl hmem))

end HeytingLean.PTS.BaseExtension
