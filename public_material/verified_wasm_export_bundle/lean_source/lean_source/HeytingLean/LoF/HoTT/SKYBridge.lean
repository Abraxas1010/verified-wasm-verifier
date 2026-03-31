import HeytingLean.LoF.HoTT.Confluence
import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.ComparisonNucleus.Examples

/-
Bridge between the tiny RT-1-based confluence result on `ΩR` and the
SKY combinator layer.

The guiding idea is:
- RT-1 says that the two "transport branches" `dec ∘ enc` and `id`
  coincide on `ΩR`, which we captured as local confluence of
  `stepComparison`.
- In the SKY layer, the combinator `I := S K K` is an identity
  combinator (`I · t` reduces to `t`).

We combine these by showing that for a chosen encoding `code` from
states into combinator terms, there is a canonical SKY term
`I · code a` that reduces to `code a`, serving as a combinatorial
join witness for the peak at `a`.
-/

namespace HeytingLean
namespace LoF
namespace HoTT

open Comb Comparison

universe u v

variable {L : Type u} {Ω : Type v}
variable [CompleteLattice L] [CompleteLattice Ω]

/-- For an arbitrary state space `α` and encoding `code : α → Comb`,
we associate to each state `a` a combinator term `I` applied to
`code a` that is guaranteed to reduce to `code a`. -/
def peakTerm {α : Type _} (code : α → Comb) (a : α) : Comb :=
  Comb.app Comb.I (code a)

/-- The SKY identity combinator witnesses that the encoded peak term
reduces to the encoded state. -/
lemma peakTerm_reduces {α : Type _} (code : α → Comb) (a : α) :
  Comb.Steps (peakTerm code a) (code a) :=
  Comb.I_reduces (t := code a)

/-- For any comparison nucleus and any encoding `code` from `ΩR` into
SKY terms, RT-1 implies that the encoded targets of a two-branch peak
have a common reduct.  Concretely, both `code b₁` and `code b₂`
reduce (trivially, via equality) to `code a`. -/
lemma comparison_peak_join_code (S : CompSpec L Ω)
    (code : ΩR S → Comb)
    {a b₁ b₂ : ΩR S}
    (h₁ : stepComparison (S := S) a b₁)
    (h₂ : stepComparison (S := S) a b₂) :
    ∃ c, Comb.Steps (code b₁) c ∧ Comb.Steps (code b₂) c := by
  -- Each branch of `stepComparison` actually returns to `a`.
  have hb₁ : b₁ = a := stepComparison_target_eq (S := S) h₁
  have hb₂ : b₂ = a := stepComparison_target_eq (S := S) h₂
  refine ⟨code a, ?_, ?_⟩
  · subst hb₁
    exact Comb.Steps.refl _
  · subst hb₂
    exact Comb.Steps.refl _

/-- A peak-term-centric join lemma: in addition to the encoded targets
`code b₁`, `code b₂` sharing a common reduct, the canonical
`peakTerm code a` also reduces to the same SKY term.  We take the join
to be `code a`, so all three terms reduce to this normal form. -/
lemma comparison_peak_join_peakTerm (S : CompSpec L Ω)
    (code : ΩR S → Comb)
    {a b₁ b₂ : ΩR S}
    (h₁ : stepComparison (S := S) a b₁)
    (h₂ : stepComparison (S := S) a b₂) :
    ∃ c,
      Comb.Steps (code b₁) c ∧
      Comb.Steps (code b₂) c ∧
      Comb.Steps (peakTerm code a) c := by
  -- As in `comparison_peak_join_code`, both targets are equal to `a`.
  have hb₁ : b₁ = a := stepComparison_target_eq (S := S) h₁
  have hb₂ : b₂ = a := stepComparison_target_eq (S := S) h₂
  refine ⟨code a, ?_, ?_, ?_⟩
  · subst hb₁
    exact Comb.Steps.refl _
  · subst hb₂
    exact Comb.Steps.refl _
  · -- The peak term reduces to `code a` by construction.
    exact peakTerm_reduces code a

/-! ### Bool specialization -/

/-- A very small encoding of Bool into SKY combinators:
`false` is represented by `K` and `true` by `S`. This choice is
arbitrary but sufficient for tiny examples. -/
def codeBool : Bool → Comb :=
  fun b => if b then Comb.S else Comb.K

lemma codeBool_injective : Function.Injective codeBool := by
  intro x y h
  cases x <;> cases y
  · -- x = false, y = false
    simp [codeBool] at h
    rfl
  · -- x = false, y = true: impossible
    simp [codeBool] at h
  · -- x = true, y = false: impossible
    simp [codeBool] at h
  · -- x = true, y = true
    simp [codeBool] at h
    rfl

/-- Using the `boolCompSpec` instance, we can regard peaks in the
two-branch system on `ΩR` (which is equivalent to Bool) and associate
to each such state a SKY term that reduces to its code. -/
noncomputable def boolPeakTerm (a : Comparison.ΩR Comparison.boolCompSpec) : Comb :=
  peakTerm codeBool (Comparison.boolΩREquiv a)

lemma boolPeakTerm_reduces
    (a : Comparison.ΩR Comparison.boolCompSpec) :
    Comb.Steps (boolPeakTerm a) (codeBool (Comparison.boolΩREquiv a)) :=
  peakTerm_reduces codeBool (Comparison.boolΩREquiv a)

/-! ### Powerset `Set (Fin 2)` specialization

This gives a slightly richer finite comparison nucleus example, whose
fixed-point core has four elements instead of two. We encode its
states combinatorially via a simple cardinality/membership scheme.
-/

open Set

/-- A tiny encoding of subsets of `Fin 2` into SKY combinators.

We distinguish the four possible sets by whether they contain `0` and
`1`, and map them to a few small terms. This is arbitrary but
adequate as a dimensional test-bed. -/
noncomputable def codeFin2 (s : Set (Fin 2)) : Comb := by
  classical
  by_cases h0 : (0 : Fin 2) ∈ s
  · -- `0 ∈ s`
    by_cases h1 : (1 : Fin 2) ∈ s
    · -- `{0,1}`: treat as a “full” state.
      exact Comb.S
    · -- `{0}` only.
      exact Comb.K
  · -- `0 ∉ s`
    by_cases h1 : (1 : Fin 2) ∈ s
    · -- `{1}` only.
      exact Comb.Y
    · -- `∅`.
      exact Comb.app Comb.K Comb.S

/-- Using the `fin2CompSpec` instance, we can regard peaks in the
two-branch system on `ΩR` (which is equivalent to `Set (Fin 2)`) and
associate to each such state a SKY term that reduces to its code. -/
noncomputable def fin2PeakTerm
    (a : Comparison.ΩR Comparison.fin2CompSpec) : Comb :=
  peakTerm codeFin2 (Comparison.fin2ΩREquiv a)

lemma fin2PeakTerm_reduces
    (a : Comparison.ΩR Comparison.fin2CompSpec) :
    Comb.Steps (fin2PeakTerm a)
      (codeFin2 (Comparison.fin2ΩREquiv a)) :=
  peakTerm_reduces codeFin2 (Comparison.fin2ΩREquiv a)

/-- Injectivity of the Boolean SKY encoding restricted to the fixed-point
core `ΩR boolCompSpec`. -/
lemma codeBool_on_ΩR_injective :
    Function.Injective
      (fun a : Comparison.ΩR Comparison.boolCompSpec =>
        codeBool (Comparison.boolΩREquiv a)) := by
  intro a b h
  -- Reduce to injectivity of `codeBool` on `Bool`.
  have hBool :
      Comparison.boolΩREquiv a =
      Comparison.boolΩREquiv b :=
    codeBool_injective (by simpa using h)
  -- `boolΩREquiv` is an equivalence whose `toFun` is projection `Subtype.val`,
  -- so equality of images implies equality of the underlying subtypes.
  cases a with
  | mk av ha =>
    cases b with
    | mk bv hb =>
      -- Rewrite `boolΩREquiv` in terms of the underlying carrier.
      dsimp [Comparison.boolΩREquiv] at hBool
      -- Equality of carriers yields equality of subtypes.
      apply Subtype.ext
      simpa using hBool

/-- For subsets of `Fin 2`, the code `Comb.S` corresponds exactly to
those sets containing both `0` and `1`. -/
lemma codeFin2_eq_S_iff (s : Set (Fin 2)) :
    codeFin2 s = Comb.S ↔
      ((0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∈ s) := by
  classical
  by_cases h0 : (0 : Fin 2) ∈ s <;>
  by_cases h1 : (1 : Fin 2) ∈ s <;>
  simp [codeFin2, h0, h1]

/-- For subsets of `Fin 2`, the code `Comb.K` corresponds exactly to
those sets containing `0` but not `1`. -/
lemma codeFin2_eq_K_iff (s : Set (Fin 2)) :
    codeFin2 s = Comb.K ↔
      ((0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∉ s) := by
  classical
  by_cases h0 : (0 : Fin 2) ∈ s <;>
  by_cases h1 : (1 : Fin 2) ∈ s <;>
  simp [codeFin2, h0, h1]

/-- For subsets of `Fin 2`, the code `Comb.Y` corresponds exactly to
those sets containing `1` but not `0`. -/
lemma codeFin2_eq_Y_iff (s : Set (Fin 2)) :
    codeFin2 s = Comb.Y ↔
      ((0 : Fin 2) ∉ s ∧ (1 : Fin 2) ∈ s) := by
  classical
  by_cases h0 : (0 : Fin 2) ∈ s <;>
  by_cases h1 : (1 : Fin 2) ∈ s <;>
  simp [codeFin2, h0, h1]

/-- For subsets of `Fin 2`, the code `K · S` corresponds exactly to
the empty set (`0` and `1` both absent). -/
lemma codeFin2_eq_KS_iff (s : Set (Fin 2)) :
    codeFin2 s = Comb.app Comb.K Comb.S ↔
      ((0 : Fin 2) ∉ s ∧ (1 : Fin 2) ∉ s) := by
  classical
  by_cases h0 : (0 : Fin 2) ∈ s <;>
  by_cases h1 : (1 : Fin 2) ∈ s <;>
  simp [codeFin2, h0, h1]

/-- `codeFin2` is injective: the four SKY codes `S`, `K`, `Y`, and
`K · S` correspond to the four possible subsets of `Fin 2`. -/
lemma codeFin2_injective : Function.Injective codeFin2 := by
  classical
  intro s t h
  -- Prove set equality by membership for each `x : Fin 2`.
  apply Set.ext
  intro x
  -- Every `x : Fin 2` is either `0` or `1`.
  have hx : x = 0 ∨ x = 1 := by
    -- Work with the underlying natural number `x.val < 2`.
    cases x with
    | mk n hn =>
      have hlt : n < 2 := hn
      -- Classify `n` as `0` or `1`.
      have hnat : n = 0 ∨ n = 1 := by
        cases n with
        | zero =>
            exact Or.inl rfl
        | succ n0 =>
            cases n0 with
            | zero =>
                -- `n = 1`
                exact Or.inr rfl
            | succ n1 =>
                -- Then `n ≥ 2`, contradicting `n < 2`.
                have hge : (2 : Nat) ≤ Nat.succ (Nat.succ n1) := by
                  exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
                have hlt' : Nat.succ (Nat.succ n1) < 2 := hlt
                have : (2 : Nat) < 2 := Nat.lt_of_le_of_lt hge hlt'
                exact (Nat.lt_irrefl _ this).elim
      -- Lift the classification back to `Fin 2` using `Fin.ext`.
      cases hnat with
      | inl h0 =>
          left
          apply Fin.ext
          simp [h0]
      | inr h1 =>
          right
          apply Fin.ext
          simp [h1]
  cases hx with
  | inl hx0 =>
      subst hx0
      constructor
      · intro hs0
        -- Use the Boolean classification for code `S`/`K`.
        by_cases hs1 : (1 : Fin 2) ∈ s
        · have hs : codeFin2 s = Comb.S := (codeFin2_eq_S_iff s).2 ⟨hs0, hs1⟩
          have ht : codeFin2 t = Comb.S := by
            simpa [hs] using h.symm
          have ht_pair := (codeFin2_eq_S_iff t).1 ht
          exact ht_pair.1
        · have hs : codeFin2 s = Comb.K := (codeFin2_eq_K_iff s).2 ⟨hs0, hs1⟩
          have ht : codeFin2 t = Comb.K := by
            simpa [hs] using h.symm
          have ht_pair := (codeFin2_eq_K_iff t).1 ht
          exact ht_pair.1
      · intro ht0
        by_cases ht1 : (1 : Fin 2) ∈ t
        · have ht : codeFin2 t = Comb.S := (codeFin2_eq_S_iff t).2 ⟨ht0, ht1⟩
          have hs : codeFin2 s = Comb.S := by
            simpa [ht] using h
          have hs_pair := (codeFin2_eq_S_iff s).1 hs
          exact hs_pair.1
        · have ht : codeFin2 t = Comb.K := (codeFin2_eq_K_iff t).2 ⟨ht0, ht1⟩
          have hs : codeFin2 s = Comb.K := by
            simpa [ht] using h
          have hs_pair := (codeFin2_eq_K_iff s).1 hs
          exact hs_pair.1
  | inr hx1 =>
      subst hx1
      constructor
      · intro hs1
        by_cases hs0 : (0 : Fin 2) ∈ s
        · have hs : codeFin2 s = Comb.S := (codeFin2_eq_S_iff s).2 ⟨hs0, hs1⟩
          have ht : codeFin2 t = Comb.S := by
            simpa [hs] using h.symm
          have ht_pair := (codeFin2_eq_S_iff t).1 ht
          exact ht_pair.2
        · have hs : codeFin2 s = Comb.Y := (codeFin2_eq_Y_iff s).2 ⟨hs0, hs1⟩
          have ht : codeFin2 t = Comb.Y := by
            simpa [hs] using h.symm
          have ht_pair := (codeFin2_eq_Y_iff t).1 ht
          exact ht_pair.2
      · intro ht1
        by_cases ht0 : (0 : Fin 2) ∈ t
        · have ht : codeFin2 t = Comb.S := (codeFin2_eq_S_iff t).2 ⟨ht0, ht1⟩
          have hs : codeFin2 s = Comb.S := by
            simpa [ht] using h
          have hs_pair := (codeFin2_eq_S_iff s).1 hs
          exact hs_pair.2
        · have ht : codeFin2 t = Comb.Y := (codeFin2_eq_Y_iff t).2 ⟨ht0, ht1⟩
          have hs : codeFin2 s = Comb.Y := by
            simpa [ht] using h
          have hs_pair := (codeFin2_eq_Y_iff s).1 hs
          exact hs_pair.2

/-- Injectivity of the `Set (Fin 2)` SKY encoding restricted to the
fixed-point core `ΩR fin2CompSpec`. -/
lemma codeFin2_on_ΩR_injective :
    Function.Injective
      (fun a : Comparison.ΩR Comparison.fin2CompSpec =>
        codeFin2 (Comparison.fin2ΩREquiv a)) := by
  classical
  intro a b h
  -- Reduce to injectivity of `codeFin2` on `Set (Fin 2)`.
  have hSet :
      Comparison.fin2ΩREquiv a =
      Comparison.fin2ΩREquiv b :=
    by
      apply codeFin2_injective
      simpa using h
  -- Equality of images under `fin2ΩREquiv` gives equality of ΩR elements.
  cases a with
  | mk av ha =>
    cases b with
    | mk bv hb =>
      dsimp [Comparison.fin2ΩREquiv] at hSet
      apply Subtype.ext
      simpa using hSet

end HoTT
end LoF
end HeytingLean
