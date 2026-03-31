import HeytingLean.PTS.BaseExtension.Contextual.Bridge
import HeytingLean.PTS.BaseExtension.Contextual.Support

namespace HeytingLean.PTS.BaseExtension.Contextual

/-!
# Semantic Support (V4) for Program-Level Bases

This file defines the V4 program-level support semantics:

- Atom: `Derives B (encode (.atom a))`
- Bot: `Derives B (encode .bot)`
- Conj: `Supports B φ ∧ Supports B ψ`
- Disj: `Derives B (encode (.disj φ ψ))` (direct derivability)
- Imp: `∀ C ⊇ B, Supports C φ → Supports C ψ`

The atom/bot/disj cases are directly derivability-based, making them trivially
equivalent to `SearchSupports` via `derives_iff_searchSupports`. The conjunction
and implication cases retain Sandqvist/elimination structure.

This replaces the former atomic-base Sandqvist semantics that was refuted on
singleton encoded disjunction. See `WIP/support_search_program_semantic_v4_probe_2026-03-19.lean`
for the discovery and audit evidence.
-/

-- ============================================================
-- § 1. V4 Semantic support definition
-- ============================================================

/--
V4 program-level support semantics. Derivability-based for atom/bot/disj,
recursive for conjunction, extension-based for implication.
-/
def Supports (B : Base) : IPL → Prop
  | .atom a => Derives B (encode (.atom a))
  | .bot => Derives B (encode .bot)
  | .conj φ ψ => Supports B φ ∧ Supports B ψ
  | .disj φ ψ => Derives B (encode (.disj φ ψ))
  | .imp φ ψ =>
      ∀ ⦃C : Base⦄, BaseExtends B C → Supports C φ → Supports C ψ

theorem supports_mono {B C : Base} (hBC : BaseExtends B C) :
    ∀ {φ : IPL}, Supports B φ → Supports C φ
  | .atom _, h => derives_mono_program hBC h
  | .bot, h => derives_mono_program hBC h
  | .conj _ _, h => ⟨supports_mono hBC h.1, supports_mono hBC h.2⟩
  | .disj _ _, h => derives_mono_program hBC h
  | .imp _ _, h =>
      by
        intro D hCD hφ
        exact h (baseExtends_trans hBC hCD) hφ

theorem supports_weaken {B : Base} {g : Goal} {φ : IPL} :
    Supports B φ → Supports (g :: B) φ :=
  supports_mono (baseExtends_cons B g)

-- ============================================================
-- § 2. Atom and bottom bridge (trivial under V4)
-- ============================================================

/--
Atom bridge: trivial under V4 — both sides are `Derives B (encode (.atom a))`.
-/
theorem atom_support_iff_search (B : Base) (a : Atom) :
    Supports B (.atom a) ↔ SearchSupports (encodeBase B) (encode (.atom a)) := by
  simp only [Supports, encodeBase]
  exact derives_iff_searchSupports

/--
Atom bridge into the new arbitrary-goal operational support surface.
-/
theorem atom_support_iff_goalSupports (B : Base) (a : Atom) :
    Supports B (.atom a) ↔ GoalSupports B (encode (.atom a)) := by
  rw [goalSupports_iff_search]
  exact atom_support_iff_search B a

/--
Bottom bridge: trivial under V4 — both sides are `Derives B (encode .bot)`.
-/
theorem bot_support_iff_search (B : Base) :
    Supports B .bot ↔ SearchSupports (encodeBase B) (encode .bot) := by
  simp only [Supports, encodeBase]
  exact derives_iff_searchSupports

/--
Bottom bridge into the new arbitrary-goal operational support surface.
-/
theorem bot_support_iff_goalSupports (B : Base) :
    Supports B .bot ↔ GoalSupports B (encode .bot) := by
  rw [goalSupports_iff_search]
  exact bot_support_iff_search B

-- ============================================================
-- § 3. Disjunction bridge (trivial under V4)
-- ============================================================

/--
Disjunction bridge: trivial under V4 — both sides are `Derives B (encode (.disj φ ψ))`.
-/
theorem disj_support_iff_search (B : Base) (φ ψ : IPL) :
    Supports B (.disj φ ψ) ↔ SearchSupports (encodeBase B) (encode (.disj φ ψ)) := by
  simp only [Supports, encodeBase]
  exact derives_iff_searchSupports

/--
Disjunction bridge into the new arbitrary-goal operational support surface.
-/
theorem disj_support_iff_goalSupports (B : Base) (φ ψ : IPL) :
    Supports B (.disj φ ψ) ↔ GoalSupports B (encode (.disj φ ψ)) := by
  rw [goalSupports_iff_search]
  exact disj_support_iff_search B φ ψ

-- ============================================================
-- § 4. Conjunction bridge (uses existing CPS extraction for atomic bases)
-- ============================================================

/--
Conjunction forward: assemble CPS conjunction search from both conjuncts.
This theorem works for general programs (no atomic restriction).
-/
theorem conj_support_implies_search (B : Base) (φ ψ : IPL)
    (ihφ : Supports B φ → SearchSupports (encodeBase B) (encode φ))
    (ihψ : Supports B ψ → SearchSupports (encodeBase B) (encode ψ)) :
    Supports B (.conj φ ψ) → SearchSupports (encodeBase B) (encode (.conj φ ψ)) := by
  intro ⟨hφ, hψ⟩
  rcases ihφ hφ with ⟨fuelφ, hfuelφ⟩
  rcases ihψ hψ with ⟨fuelψ, hfuelψ⟩
  let P := encodeBase B
  let fuel := fuelφ + fuelψ
  have hφ' : search fuel P (encode φ) = true :=
    search_fuel_mono fuelφ fuelψ P (encode φ) hfuelφ
  have hψ' : search fuel P (encode ψ) = true := by
    have := search_fuel_mono fuelψ fuelφ P (encode ψ) hfuelψ
    rwa [Nat.add_comm] at this
  let c := freshAtomForGoal P
    (Goal.imp
      (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
      (Goal.atom (.bvar 0)))
  let K : Goal := Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.atom c)))
  have hφ_w : search fuel (K :: P) (encode φ) = true :=
    search_weaken fuel P [K] (encode φ) hφ'
  have hψ_w : search fuel (K :: P) (encode ψ) = true :=
    search_weaken fuel P [K] (encode ψ) hψ'
  have hφ3 : search (fuel + 3) (K :: P) (encode φ) = true :=
    search_fuel_mono fuel 3 (K :: P) (encode φ) hφ_w
  have hψ3 : search (fuel + 2) (K :: P) (encode ψ) = true :=
    search_fuel_mono fuel 2 (K :: P) (encode ψ) hψ_w
  have hc_fires : fires (fuel + 3) (K :: P) (.atom (.atom c)) (.atom c) = true := by
    have : fuel + 3 = (fuel + 2).succ := by omega
    rw [this, fires.eq_2]; simp
  have hψ_fires : fires (fuel + 4) (K :: P) (.imp (encode ψ) (.atom (.atom c))) (.atom c) = true := by
    have : fuel + 4 = (fuel + 3).succ := by omega
    rw [this, fires.eq_3, Bool.and_eq_true]
    exact ⟨search_fuel_mono (fuel + 2) 1 (K :: P) (encode ψ) hψ3, hc_fires⟩
  have hK_fires : fires (fuel + 5) (K :: P)
      (.imp (encode φ) (.imp (encode ψ) (.atom (.atom c)))) (.atom c) = true := by
    have : fuel + 5 = (fuel + 4).succ := by omega
    rw [this, fires.eq_3, Bool.and_eq_true]
    exact ⟨search_fuel_mono (fuel + 3) 1 (K :: P) (encode φ) hφ3, hψ_fires⟩
  have hSAA : searchAnyAssumption (fuel + 5) (K :: P) (K :: P) (.atom c) = true := by
    simp only [searchAnyAssumption, Bool.or_eq_true]
    exact Or.inl hK_fires
  refine ⟨fuel + 8, ?_⟩
  have h8 : fuel + 8 = (fuel + 7).succ := by omega
  have h7 : fuel + 7 = (fuel + 6).succ := by omega
  have h6 : fuel + 6 = (fuel + 5).succ := by omega
  rw [encode, h8, search.eq_6]
  simp only [substGoal, substAtomVar, substGoal_encode]
  rw [h7, search.eq_3, h6, search.eq_2]
  exact hSAA

/--
Conjunction backward, factored through the exact remaining head-search premise.

This theorem does not pretend the arbitrary-program extractor is already proved.
It packages the new `Bridge`-level extractor theorems into the semantic bridge
surface so the live blocker is a single explicit hypothesis rather than an
informal note.
-/
theorem conj_search_implies_support_of_head_search (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftHeadSearch :
      ∀ {a : Atom} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true)
    (hRightHeadSearch :
      ∀ {a : Atom} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_head_search
        (P := encodeBase B) φ ψ hLeftHeadSearch h
  · exact ihψ <|
      cps_conj_extract_right_of_head_search
        (P := encodeBase B) φ ψ hRightHeadSearch h

/--
Conjunction backward through a weaker resolution premise.

Unlike the stricter head-search packaging, this allows the fresh-atom branch to
resolve either by proving that the conjunction head fired or by proving that the
target conjunct already searches from the ambient program. The bounded
head-search audit shows this weaker shape is necessary: there are small
programs where the stricter head-search premise fails even though conjunction
search and both conjunct searches still hold.
-/
theorem conj_search_implies_support_of_resolution (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftResolve :
      ∀ {a : Atom} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true ∨
            SearchSupports (encodeBase B) (encode φ))
    (hRightResolve :
      ∀ {a : Atom} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true ∨
            SearchSupports (encodeBase B) (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_resolution
        (P := encodeBase B) φ ψ hLeftResolve h
  · exact ihψ <|
      cps_conj_extract_right_of_resolution
        (P := encodeBase B) φ ψ hRightResolve h

/--
Conjunction backward through an ambient-clause classification premise.

This is a tighter theorem surface than the raw weakened-resolution Bool premise:
the ambient branch is no longer hidden behind `searchAnyAssumption = true`, but
is presented as explicit focused evidence that some ambient clause in
`encodeBase B` fired to the fresh continuation atom.
-/
theorem conj_search_implies_support_of_ambient_clause (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftAmbient :
      ∀ {a : Atom} {D : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        D ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          D
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hRightAmbient :
      ∀ {a : Atom} {D : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        D ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          D
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_ambient_clause
        (P := encodeBase B) φ ψ hLeftAmbient h
  · exact ihψ <|
      cps_conj_extract_right_of_ambient_clause
        (P := encodeBase B) φ ψ hRightAmbient h

/--
Conjunction backward through constructor-classified ambient clauses.

This is the sharpened ambient theorem surface after the constructor split:
the only remaining ambient branches are implication clauses and universal
clauses, which can now be handled independently.
-/
theorem conj_search_implies_support_of_ambient_constructor_cases (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all g ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all g)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hRightAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all g ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all g)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_ambient_constructor_cases
        (P := encodeBase B) φ ψ hLeftAmbientImp hLeftAmbientAll h
  · exact ihψ <|
      cps_conj_extract_right_of_ambient_constructor_cases
        (P := encodeBase B) φ ψ hRightAmbientImp hRightAmbientAll h

theorem conj_search_implies_support_of_ambient_all_member_cases (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ g₂) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ g₂))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hRightAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ g₂) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ g₂))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_ambient_all_member_cases
        (P := encodeBase B) φ ψ hLeftAmbientImp hLeftAmbientAllImp hLeftAmbientAllAll h
  · exact ihψ <|
      cps_conj_extract_right_of_ambient_all_member_cases
        (P := encodeBase B) φ ψ hRightAmbientImp hRightAmbientAllImp hRightAmbientAllAll h

/--
Conjunction backward through the exact recursive ambient-`all imp` tail split.

The ambient universal implication branch is no longer a single opaque callback.
Its tail is classified into the three genuinely live cases:

- `∀X.(g₁ -> X)` (top-tail)
- `∀X.(g₁ -> (u -> v))`
- `∀X.(g₁ -> ∀Y.u)`

plus the separate ambient `.all (.all g)` branch.
-/
theorem conj_search_implies_support_of_ambient_all_imp_tail_cases (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpTop :
      ∀ {a : Atom} {g₁ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.imp u v)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.all u)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hRightAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpTop :
      ∀ {a : Atom} {g₁ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.imp u v)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.all u)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_ambient_all_imp_tail_cases
        (P := encodeBase B) φ ψ
        hLeftAmbientImp hLeftAmbientAllImpTop hLeftAmbientAllImpImp
        hLeftAmbientAllImpAll hLeftAmbientAllAll h
  · exact ihψ <|
      cps_conj_extract_right_of_ambient_all_imp_tail_cases
        (P := encodeBase B) φ ψ
        hRightAmbientImp hRightAmbientAllImpTop hRightAmbientAllImpImp
        hRightAmbientAllImpAll hRightAmbientAllAll h

/--
Conjunction backward through the root-filtered ambient-`all imp` split.

The generic top-tail callback is no longer required as a single opaque premise.
It is split by premise root:

- `∀X.((atom v) -> X)`
- `∀X.((u -> v) -> X)`
- `∀X.((u ∨ v) -> X)`
- `∀X.((∀Y.u) -> X)`

and the Bridge layer discharges the closed and theoremized one-hole
implication subfamilies locally before consulting the residual root callback.
-/
theorem conj_search_implies_support_of_ambient_all_imp_root_cases (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpTopAtom :
      ∀ {a : Atom} {v : AtomVar} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.atom v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.atom v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpTopImp :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.imp u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.imp u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpTopDisj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.disj u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.disj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpTopConj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.conj u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.conj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpTopAll :
      ∀ {a : Atom} {u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.all u) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.all u) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.imp u v)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.all u)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hRightAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpTopAtom :
      ∀ {a : Atom} {v : AtomVar} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.atom v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.atom v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpTopImp :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.imp u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.imp u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpTopDisj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.disj u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.disj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpTopConj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.conj u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.conj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpTopAll :
      ∀ {a : Atom} {u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.all u) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.all u) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.imp u v)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.all u)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_ambient_all_imp_root_cases
        (P := encodeBase B) φ ψ
        hLeftAmbientImp hLeftAmbientAllImpTopAtom hLeftAmbientAllImpTopImp
        hLeftAmbientAllImpTopDisj hLeftAmbientAllImpTopConj hLeftAmbientAllImpTopAll
        hLeftAmbientAllImpImp hLeftAmbientAllImpAll hLeftAmbientAllAll h
  · exact ihψ <|
      cps_conj_extract_right_of_ambient_all_imp_root_cases
        (P := encodeBase B) φ ψ
        hRightAmbientImp hRightAmbientAllImpTopAtom hRightAmbientAllImpTopImp
        hRightAmbientAllImpTopDisj hRightAmbientAllImpTopConj hRightAmbientAllImpTopAll
        hRightAmbientAllImpImp hRightAmbientAllImpAll hRightAmbientAllAll h

/--
Conjunction backward through the root-filtered ambient-`all imp` split, with
the residual top-`conj` callback family lifted into the goal-level semantics.

The `prem = conj _ _` branch now receives the two instantiated conjunct goals as
`HeadGoalSupportsCtx` obligations in the witness head context and returns an
ambient `GoalSupports` conclusion. The other root branches remain on the
existing operational surface for now.
-/
theorem conj_search_implies_support_of_ambient_all_imp_root_cases_goal_top_conj
    (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpTopAtom :
      ∀ {a : Atom} {v : AtomVar} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.atom v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.atom v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpTopImp :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.imp u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.imp u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpTopDisj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.disj u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.disj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpTopConj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.conj u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.conj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal u 0 a) →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal v 0 a) →
        GoalSupports B (encode φ))
    (hLeftAmbientAllImpTopAll :
      ∀ {a : Atom} {u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.all u) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.all u) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.imp u v)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.all u)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hRightAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpTopAtom :
      ∀ {a : Atom} {v : AtomVar} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.atom v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.atom v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpTopImp :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.imp u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.imp u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpTopDisj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.disj u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.disj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpTopConj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.conj u v) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.conj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal u 0 a) →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal v 0 a) →
        GoalSupports B (encode ψ))
    (hRightAmbientAllImpTopAll :
      ∀ {a : Atom} {u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp (.all u) (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp (.all u) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.imp u v)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.all u)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_ambient_all_imp_root_cases_goal_top_conj
        (P := encodeBase B) φ ψ
        hLeftAmbientImp hLeftAmbientAllImpTopAtom hLeftAmbientAllImpTopImp
        hLeftAmbientAllImpTopDisj hLeftAmbientAllImpTopConj hLeftAmbientAllImpTopAll
        hLeftAmbientAllImpImp hLeftAmbientAllImpAll hLeftAmbientAllAll h
  · exact ihψ <|
      cps_conj_extract_right_of_ambient_all_imp_root_cases_goal_top_conj
        (P := encodeBase B) φ ψ
        hRightAmbientImp hRightAmbientAllImpTopAtom hRightAmbientAllImpTopImp
        hRightAmbientAllImpTopDisj hRightAmbientAllImpTopConj hRightAmbientAllImpTopAll
        hRightAmbientAllImpImp hRightAmbientAllImpAll hRightAmbientAllAll h

/--
Conjunction backward through the root-filtered ambient-`all imp` split, with
the full top-tail `∀X.(prem -> X)` family lifted into the goal-level semantics.

The remaining raw operational debt is now only in the recursive tail branches
`∀X.(g₁ -> (u -> v))` and `∀X.(g₁ -> ∀Y.u)` plus the separate `∀X.∀Y.g`
family; all top-tail arbitrary-premise callbacks are semantic.
-/
theorem conj_search_implies_support_of_ambient_all_imp_root_cases_goal_top
    (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpTop :
      ∀ {a : Atom} {prem : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp prem (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp prem (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal prem 0 a) →
        GoalSupports B (encode φ))
    (hLeftAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.imp u v)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.all u)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hLeftAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode φ))
    (hRightAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpTop :
      ∀ {a : Atom} {prem : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp prem (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp prem (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal prem 0 a) →
        GoalSupports B (encode ψ))
    (hRightAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.imp u v)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.all u)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ))
    (hRightAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports (encodeBase B) (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_ambient_all_imp_root_cases_goal_top
        (P := encodeBase B) φ ψ
        hLeftAmbientImp hLeftAmbientAllImpTop
        hLeftAmbientAllImpImp hLeftAmbientAllImpAll hLeftAmbientAllAll h
  · exact ihψ <|
      cps_conj_extract_right_of_ambient_all_imp_root_cases_goal_top
        (P := encodeBase B) φ ψ
        hRightAmbientImp hRightAmbientAllImpTop
        hRightAmbientAllImpImp hRightAmbientAllImpAll hRightAmbientAllAll h

/--
Conjunction backward through the root-filtered ambient-`all imp` split, with
the recursive ambient tail callbacks lifted into the mixed goal-support /
goal-fire semantic surface.

This extends `...goal_top`: the top-tail arbitrary-premise family already uses
`HeadGoalSupportsCtx`; the remaining recursive tails now also speak semantically
through `HeadGoalFiresCtx`.
-/
theorem conj_search_implies_support_of_ambient_all_imp_root_cases_goal_fire
    (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          g₁ →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          g₂
          (.atom a) →
        GoalSupports B (encode φ))
    (hLeftAmbientAllImpTop :
      ∀ {a : Atom} {prem : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp prem (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp prem (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal prem 0 a) →
        GoalSupports B (encode φ))
    (hLeftAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.imp u v)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal g₁ 0 a) →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal (.imp u v) 0 a)
          (.atom a) →
        GoalSupports B (encode φ))
    (hLeftAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.all u)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal g₁ 0 a) →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal (.all u) 0 a)
          (.atom a) →
        GoalSupports B (encode φ))
    (hLeftAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal (substGoal g 1 a) 0 a)
          (.atom a) →
        GoalSupports B (encode φ))
    (hRightAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.imp g₁ g₂ ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.imp g₁ g₂)
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          g₁ →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          g₂
          (.atom a) →
        GoalSupports B (encode ψ))
    (hRightAmbientAllImpTop :
      ∀ {a : Atom} {prem : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp prem (.atom (.bvar 0))) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp prem (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal prem 0 a) →
        GoalSupports B (encode ψ))
    (hRightAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.imp u v)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal g₁ 0 a) →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal (.imp u v) 0 a)
          (.atom a) →
        GoalSupports B (encode ψ))
    (hRightAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.imp g₁ (.all u)) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal g₁ 0 a) →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal (.all u) 0 a)
          (.atom a) →
        GoalSupports B (encode ψ))
    (hRightAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        Goal.all (.all g) ∈ encodeBase B →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (.all (.all g))
          (.atom a) = true →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal (substGoal g 1 a) 0 a)
          (.atom a) →
        GoalSupports B (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_ambient_all_imp_root_cases_goal_fire
        (P := encodeBase B) φ ψ
        hLeftAmbientImp hLeftAmbientAllImpTop
        hLeftAmbientAllImpImp hLeftAmbientAllImpAll hLeftAmbientAllAll h
  · exact ihψ <|
      cps_conj_extract_right_of_ambient_all_imp_root_cases_goal_fire
        (P := encodeBase B) φ ψ
        hRightAmbientImp hRightAmbientAllImpTop
        hRightAmbientAllImpImp hRightAmbientAllImpAll hRightAmbientAllAll h

/--
Conjunction backward through the single remaining universal-body obstruction.

Ambient implication clauses no longer need their own theorem family: they reduce
to the same-atom universal-body firing obstruction handled by `hLeftAllBody`
and `hRightAllBody`.
-/
theorem conj_search_implies_support_of_all_body_obstruction (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftAllBody :
      ∀ {a : Atom} {body : Goal},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        a ∉ goalAtoms body →
        Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (substGoal body 0 a)
          (.atom a) →
        SearchSupports (encodeBase B) (encode φ))
    (hRightAllBody :
      ∀ {a : Atom} {body : Goal},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        a ∉ goalAtoms body →
        Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: encodeBase B)
          (substGoal body 0 a)
          (.atom a) →
        SearchSupports (encodeBase B) (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_all_body_obstruction
        (P := encodeBase B) φ ψ hLeftAllBody h
  · exact ihψ <|
      cps_conj_extract_right_of_all_body_obstruction
        (P := encodeBase B) φ ψ hRightAllBody h

/--
Conjunction backward through the remaining universal-body obstruction, stated
through the goal-target firing semantics.

This is the first honest consumer of the successor language: the residual
obstruction is no longer phrased in terms of raw `Fires`, but in terms of
`HeadGoalFiresCtx` on the witness head context.
-/
theorem conj_search_implies_support_of_all_body_obstruction_goal_fire
    (B : Base) (φ ψ : IPL)
    (ihφ : SearchSupports (encodeBase B) (encode φ) → Supports B φ)
    (ihψ : SearchSupports (encodeBase B) (encode ψ) → Supports B ψ)
    (hLeftAllBody :
      ∀ {a : Atom} {body : Goal},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms (encodeBase B) →
        a ∉ goalAtoms body →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal body 0 a)
          (.atom a) →
        GoalSupports B (encode φ))
    (hRightAllBody :
      ∀ {a : Atom} {body : Goal},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms (encodeBase B) →
        a ∉ goalAtoms body →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          B
          (substGoal body 0 a)
          (.atom a) →
        GoalSupports B (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.conj φ ψ)) → Supports B (.conj φ ψ) := by
  intro h
  refine ⟨?_, ?_⟩
  · exact ihφ <|
      cps_conj_extract_left_of_all_body_obstruction
        (P := encodeBase B) φ ψ
        (fun {a} {body} haEncodeφ haP haBody hBodyFire => by
          have hFireCtx :
              HeadGoalFiresCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                B
                (substGoal body 0 a)
                (.atom a) := by
            rw [headGoalFiresCtx_iff_firesCtx]
            simpa [encodeBase] using hBodyFire
          have hGoal : GoalSupports B (encode φ) :=
            hLeftAllBody haEncodeφ haP haBody hFireCtx
          rw [goalSupports_iff_search] at hGoal
          exact hGoal)
        h
  · exact ihψ <|
      cps_conj_extract_right_of_all_body_obstruction
        (P := encodeBase B) φ ψ
        (fun {a} {body} haEncodeψ haP haBody hBodyFire => by
          have hFireCtx :
              HeadGoalFiresCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                B
                (substGoal body 0 a)
                (.atom a) := by
            rw [headGoalFiresCtx_iff_firesCtx]
            simpa [encodeBase] using hBodyFire
          have hGoal : GoalSupports B (encode ψ) :=
            hRightAllBody haEncodeψ haP haBody hFireCtx
          rw [goalSupports_iff_search] at hGoal
          exact hGoal)
        h

/--
Implication backward: if `encode (φ → ψ)` searches from `B`, then the V4 semantic
implication clause holds at `B`.

This is the clean consumer of the landed general `search_cut`: after lifting the
search witness from `B` to any extension `C`, cut composes the antecedent search
in `C` with the searchable consequent in `encode φ :: C`.
-/
theorem imp_search_implies_support (B : Base) (φ ψ : IPL)
    (ihφ : ∀ C : Base, Supports C φ ↔ SearchSupports (encodeBase C) (encode φ))
    (ihψ : ∀ C : Base, Supports C ψ ↔ SearchSupports (encodeBase C) (encode ψ)) :
    SearchSupports (encodeBase B) (encode (.imp φ ψ)) → Supports B (.imp φ ψ) := by
  intro hSearch C hBC hφ
  rcases hSearch with ⟨fuel, hfuel⟩
  cases fuel with
  | zero =>
      simp [search] at hfuel
  | succ fuel =>
      rw [encode, search.eq_3] at hfuel
      have hMono : ∀ x, x ∈ encode φ :: encodeBase B → x ∈ encode φ :: encodeBase C := by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (encodeBase_mono hBC x hx)
      have hψSearchHead : SearchSupports (encode φ :: encodeBase C) (encode ψ) := by
        exact ⟨fuel, search_mono_program fuel _ _ _ hMono hfuel⟩
      have hφSearch : SearchSupports (encodeBase C) (encode φ) :=
        (ihφ C).mp hφ
      exact (ihψ C).mpr <|
        search_cut (P := encodeBase C) (d := encode φ) (g := encode ψ) hφSearch hψSearchHead

-- ============================================================
-- § 5. Legacy status
-- ============================================================

/--
Status marker for the V4 program-level bridge.

The V4 semantic candidate replaces the former atomic-base Sandqvist semantics.
The atom/bot/disjunction cases are trivial and implication backward now consumes
the landed general `search_cut`. A bounded direct V4 audit has now retired the
blanket implication-forward bridge shape itself: in the curated size-3 fragment,
`SupportsV4 P ((p0 \/ p1) -> p0)` can hold while
`SearchSupports P (encode ((p0 \/ p1) -> p0))` fails nonvacuously. So the
remaining honest work is no longer "prove a global support_iff_search somehow".
The parent program-base generalization project is complete as a misformalized
closeout: program-level `Base`, V4 semantics, `search_cut`, and implication
backward all landed, while the original global bridge target diverged from the
actual V4/kernel truth. A second bounded audit on 2026-03-24 retires the
stronger intermediate route that tried to package conjunction backward through a
global "fresh atom search must have come from the conjunction head" premise:
there is already a length-2 witness where that premise fails while conjunction
search and both conjunct searches still succeed. So
`conj_search_implies_support_of_head_search` should be treated as a conditional
packaging theorem, not as the parent project's closeout target. The remaining
theorem work was then narrowed to
`support_search_v4_conjunction_backward_followon_20260325`, but that successor
is now also retired as misformalized: bounded audits stayed clean on the live
conjunction surfaces, while the remaining callback hypotheses quantify over
arbitrary `Goal` premises that the formula-level `Supports` semantics cannot
state or discharge. The honest successor is therefore
`support_search_v4_goal_support_generalization_20260325`, which tracks the
needed semantic generalization from IPL formulas to arbitrary goal clauses (or
an equivalent clause-local judgment). The mandatory pre-flight gate remains
`./scripts/support_search_phase3_gate.sh`: it must see `search_cut` and the
bridge exports through imports before any further conjunction-focused proof
step. The bounded witnesses are recorded at
`WIP/phase3_direct_v4_bridge_probe_2026-03-24.lean` and
`artifacts/ops/support_search_phase3_headsearch_audit_20260324/len2_fuel12.json`.
-/
def legacySemanticSupportStatus : String :=
  "V4 program-level semantics: atom/bot/disj trivial via derives_iff_searchSupports; conj forward proved; imp backward proved via search_cut. The parent program-base generalization project closes as misformalized: the blanket implication-forward bridge shape is retired by bounded/kernel evidence, the stronger global head-search packaging for conjunction backward is also retired, and the narrower conjunction-follow-on was itself retired as misformalized once the residual callbacks were recognized as arbitrary Goal-level obligations outside the current formula-level Supports semantics. The remaining real theorem work is isolated to support_search_v4_goal_support_generalization_20260325. Run scripts/support_search_phase3_gate.sh before any further conjunction follow-on proof step so stale exports fail closed."

end Contextual
end HeytingLean.PTS.BaseExtension
