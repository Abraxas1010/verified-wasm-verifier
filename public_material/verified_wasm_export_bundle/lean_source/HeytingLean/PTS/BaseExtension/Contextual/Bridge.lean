import HeytingLean.PTS.BaseExtension.Contextual.Encoding
import HeytingLean.PTS.BaseExtension.Contextual.Derives
import HeytingLean.PTS.BaseExtension.Contextual.Support

namespace HeytingLean.PTS.BaseExtension.Contextual

/-!
# Bridge Infrastructure for Support↔Search

This file provides the key lemmas needed for the contextual Support↔Search
bridge theorem (Gheorghiu, arXiv:2603.13018v1, Theorem 4.6):

- `Neutral`: goals built from atom/imp/all only (no raw conj/disj)
- `encode_neutral`: the CPS encoding always produces Neutral goals
- Fuel and program monotonicity for search/fires

Note: With `Base = Program` and `encodeBase = id`, theorems that depended on
the atomic structure of `encodeBase B = B.atoms.map (...)` are now parametrized
over `(atoms : List Atom)` and use `atomicBase atoms` explicitly.
-/

-- ============================================================
-- § 1. Neutral goals
-- ============================================================

/--
A goal is *neutral* if it uses only atom, imp, and all constructors.
The CPS encoding produces only neutral goals, and the `fires` function
handles all neutral goals correctly (it returns false on conj/disj).
This corresponds to Lemma 4.3 of the paper.
-/
inductive Neutral : Goal → Prop where
  | atom (v : AtomVar) : Neutral (.atom v)
  | imp {g₁ g₂ : Goal} : Neutral g₁ → Neutral g₂ → Neutral (.imp g₁ g₂)
  | all {g : Goal} : Neutral g → Neutral (.all g)

theorem encode_neutral : ∀ (φ : IPL), Neutral (encode φ) := by
  intro φ
  induction φ with
  | atom p => exact Neutral.atom (.atom p)
  | bot => exact Neutral.all (Neutral.atom (.bvar 0))
  | conj φ ψ ihφ ihψ =>
      exact Neutral.all
        (Neutral.imp
          (Neutral.imp ihφ (Neutral.imp ihψ (Neutral.atom (.bvar 0))))
          (Neutral.atom (.bvar 0)))
  | disj φ ψ ihφ ihψ =>
      exact Neutral.all
        (Neutral.imp
          (Neutral.imp ihφ (Neutral.atom (.bvar 0)))
          (Neutral.imp
            (Neutral.imp ihψ (Neutral.atom (.bvar 0)))
            (Neutral.atom (.bvar 0))))
  | imp φ ψ ihφ ihψ =>
      exact Neutral.imp ihφ ihψ

theorem neutral_substGoal {g : Goal} (n : Nat) (a : Atom) :
    Neutral g → Neutral (substGoal g n a) := by
  intro h
  induction h generalizing n with
  | atom v =>
      simp [substGoal]
      exact Neutral.atom _
  | imp h₁ h₂ ih₁ ih₂ =>
      simp [substGoal]
      exact Neutral.imp (ih₁ n) (ih₂ n)
  | all h ih =>
      simp [substGoal]
      exact Neutral.all (ih (n + 1))

-- ============================================================
-- § 2. Program monotonicity (weakening)
-- ============================================================

-- The ∀ case in search picks freshAtomForGoal P g, which changes when P grows.
-- We avoid the renaming problem by observing:
-- (1) fires for .atom targets use the target atom for substitution, not freshAtomForGoal
-- (2) fires for .bvar targets DO use freshAtomForGoal — but .bvar targets only arise
--     from un-substituted bound variables, which don't occur in well-formed search goals
-- (3) The ∀ case in search always substitutes into the goal, producing .atom targets
--
-- For the bridge theorem, all goals are encode φ which are closed (no free bvars).
-- We prove weakening for closed goals directly.

/-- A goal is closed (has no free bound variables above depth d). -/
def Closed (d : Nat) : Goal → Prop
  | .atom (.atom _) => True
  | .atom (.bvar n) => n < d
  | .imp g₁ g₂ => Closed d g₁ ∧ Closed d g₂
  | .conj g₁ g₂ => Closed d g₁ ∧ Closed d g₂
  | .disj g₁ g₂ => Closed d g₁ ∧ Closed d g₂
  | .all g => Closed (d + 1) g

private theorem closed_mono {d : Nat} {g : Goal} (h : Closed d g) : Closed (d + 1) g := by
  induction g generalizing d with
  | atom v => cases v with
    | atom _ => trivial
    | bvar n => simp [Closed] at h ⊢; omega
  | imp g₁ g₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | conj g₁ g₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | disj g₁ g₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | all g ih => exact ih h

theorem encode_closed : ∀ (φ : IPL), Closed 0 (encode φ) := by
  intro φ
  induction φ with
  | atom _ => simp [encode, Closed]
  | bot => simp [encode, Closed]
  | conj _ _ ihφ ihψ =>
      simp only [encode, Closed]
      exact ⟨⟨closed_mono ihφ, closed_mono ihψ, Nat.zero_lt_succ 0⟩, Nat.zero_lt_succ 0⟩
  | disj _ _ ihφ ihψ =>
      simp only [encode, Closed]
      exact ⟨⟨closed_mono ihφ, Nat.zero_lt_succ 0⟩, ⟨closed_mono ihψ, Nat.zero_lt_succ 0⟩, Nat.zero_lt_succ 0⟩
  | imp _ _ ihφ ihψ => exact ⟨ihφ, ihψ⟩

/-- Substituting at or beyond the binding depth leaves a closed goal unchanged. -/
theorem substGoal_closed {g : Goal} {n d : Nat} {a : Atom} (h : Closed d g) (hnd : d ≤ n) :
    substGoal g n a = g := by
  induction g generalizing d n with
  | atom v =>
      cases v with
      | atom _ => simp [substGoal, substAtomVar]
      | bvar k =>
          simp [substGoal, substAtomVar]
          have hk : k < d := h
          have : k ≠ n := by omega
          simp [this]
  | imp g₁ g₂ ih₁ ih₂ =>
      simp [substGoal, ih₁ h.1 hnd, ih₂ h.2 hnd]
  | conj g₁ g₂ ih₁ ih₂ =>
      simp [substGoal, ih₁ h.1 hnd, ih₂ h.2 hnd]
  | disj g₁ g₂ ih₁ ih₂ =>
      simp [substGoal, ih₁ h.1 hnd, ih₂ h.2 hnd]
  | all g ih =>
      simp [substGoal, ih h (Nat.succ_le_succ hnd)]

theorem substGoal_encode (φ : IPL) (n : Nat) (a : Atom) :
    substGoal (encode φ) n a = encode φ :=
  substGoal_closed (encode_closed φ) (Nat.zero_le _)

mutual
  /--
  Goal-level substitution for bound continuation variables.

  This is the syntactic operation missing from the atom-level kernel substitution
  `substGoal`: when a CPS encoding quantifies over a result goal `X`, later Phase 3
  bridge arguments need to instantiate `X` with a closed goal such as `encode φ`,
  not merely with a fresh atom.
  -/
  def substGoalWithGoal (g : Goal) (n : Nat) (h : Goal) : Goal :=
    match g with
    | .atom (.atom a) => .atom (.atom a)
    | .atom (.bvar k) => if k = n then h else .atom (.bvar k)
    | .imp g₁ g₂ => .imp (substGoalWithGoal g₁ n h) (substGoalWithGoal g₂ n h)
    | .conj g₁ g₂ => .conj (substGoalWithGoal g₁ n h) (substGoalWithGoal g₂ n h)
    | .disj g₁ g₂ => .disj (substGoalWithGoal g₁ n h) (substGoalWithGoal g₂ n h)
    | .all g' => .all (substGoalWithGoal g' (n + 1) h)
end

theorem neutral_substGoalWithGoal {g h : Goal} (n : Nat) :
    Neutral g → Neutral h → Neutral (substGoalWithGoal g n h) := by
  intro hg hh
  induction hg generalizing n h with
  | atom v =>
      cases v with
      | atom a =>
          simp [substGoalWithGoal]
          exact Neutral.atom (.atom a)
      | bvar k =>
          by_cases hk : k = n
          · simp [substGoalWithGoal, hk]
            exact hh
          · simp [substGoalWithGoal, hk]
            exact Neutral.atom (.bvar k)
  | imp hg₁ hg₂ ih₁ ih₂ =>
      simp [substGoalWithGoal]
      exact Neutral.imp (ih₁ n hh) (ih₂ n hh)
  | all hg ih =>
      simp [substGoalWithGoal]
      exact Neutral.all (ih (n + 1) hh)

theorem substGoalWithGoal_closed {g h : Goal} {n d : Nat}
    (hg : Closed d g) (hdn : d ≤ n) :
    substGoalWithGoal g n h = g := by
  induction g generalizing d n h with
  | atom v =>
      cases v with
      | atom a =>
          simp [substGoalWithGoal]
      | bvar k =>
          simp [Closed] at hg
          by_cases hk : k = n
          · subst hk
            omega
          · simp [substGoalWithGoal, hk]
  | imp g₁ g₂ ih₁ ih₂ =>
      exact by
        simp [Closed] at hg
        simp [substGoalWithGoal, ih₁ hg.1 hdn, ih₂ hg.2 hdn]
  | conj g₁ g₂ ih₁ ih₂ =>
      exact by
        simp [Closed] at hg
        simp [substGoalWithGoal, ih₁ hg.1 hdn, ih₂ hg.2 hdn]
  | disj g₁ g₂ ih₁ ih₂ =>
      exact by
        simp [Closed] at hg
        simp [substGoalWithGoal, ih₁ hg.1 hdn, ih₂ hg.2 hdn]
  | all g ih =>
      exact by
        simp [Closed] at hg
        simp [substGoalWithGoal, ih hg (Nat.succ_le_succ hdn)]

theorem substGoalWithGoal_encode_conj_body
    (φ ψ : IPL) (h : Goal) :
    substGoalWithGoal
        (Goal.imp
          (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
          (Goal.atom (.bvar 0)))
        0 h =
      Goal.imp
        (Goal.imp (encode φ) (Goal.imp (encode ψ) h))
        h := by
  simp [substGoalWithGoal, substGoalWithGoal_closed (h := h) (encode_closed φ) (Nat.zero_le _),
    substGoalWithGoal_closed (h := h) (encode_closed ψ) (Nat.zero_le _)]

theorem substGoalWithGoal_encode_disj_body
    (φ ψ : IPL) (h : Goal) :
    substGoalWithGoal
        (Goal.imp
          (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
          (Goal.imp
            (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
            (Goal.atom (.bvar 0))))
        0 h =
      Goal.imp
        (Goal.imp (encode φ) h)
        (Goal.imp (Goal.imp (encode ψ) h) h) := by
  simp [substGoalWithGoal, substGoalWithGoal_closed (h := h) (encode_closed φ) (Nat.zero_le _),
    substGoalWithGoal_closed (h := h) (encode_closed ψ) (Nat.zero_le _)]

/--
Any already-derived goal can be used as the consequent of a derivable implication.

This is the minimal derivation-side consumer of the new goal-level substitution
surface: once the continuation goal is derivable, CPS bodies instantiated at that
goal become derivable by implication introduction plus weakening.
-/
theorem derives_imp_of_derived {P : Program} {g h : Goal} :
    Derives P h → Derives P (.imp g h) := by
  intro hh
  exact Derives.imp (derives_weaken (extras := [g]) hh)

theorem search_imp_of_derived {P : Program} {g h : Goal} :
    SearchSupports P h → SearchSupports P (.imp g h) := by
  intro hh
  exact derives_iff_searchSupports.mp <|
    derives_imp_of_derived (g := g) (derives_iff_searchSupports.mpr hh)

/--
If `encode φ` supports itself when added as a head assumption, then the standard
left conjunction continuation `φ → ψ → φ` is derivable in any ambient program.

This packages the exact continuation used by conjunction backward, separating the
transport problem from the purely structural continuation-construction step.
-/
theorem derives_cps_conj_left_cont_of_self_support
    (φ ψ : IPL)
    (ihφ : ∀ Q : Program, Derives (encode φ :: Q) (encode φ))
    (P : Program) :
    Derives P (Goal.imp (encode φ) (Goal.imp (encode ψ) (encode φ))) := by
  have hBody : Derives (encode ψ :: encode φ :: P) (encode φ) := by
    exact derives_of_program_memeq
      (P := encode φ :: encode ψ :: P)
      (Q := encode ψ :: encode φ :: P)
      (g := encode φ)
      (by
        intro x
        simp [or_left_comm])
      (ihφ (encode ψ :: P))
  exact Derives.imp (Derives.imp hBody)

theorem search_cps_conj_left_cont_of_self_support
    (φ ψ : IPL)
    (ihφ : ∀ Q : Program, SearchSupports (encode φ :: Q) (encode φ))
    (P : Program) :
    SearchSupports P (Goal.imp (encode φ) (Goal.imp (encode ψ) (encode φ))) := by
  exact derives_iff_searchSupports.mp <|
    derives_cps_conj_left_cont_of_self_support φ ψ
      (fun Q => derives_iff_searchSupports.mpr (ihφ Q))
      P

/--
If `encode ψ` supports itself when added as a head assumption, then the standard
right conjunction continuation `φ → ψ → ψ` is derivable in any ambient program.
-/
theorem derives_cps_conj_right_cont_of_self_support
    (φ ψ : IPL)
    (ihψ : ∀ Q : Program, Derives (encode ψ :: Q) (encode ψ))
    (P : Program) :
    Derives P (Goal.imp (encode φ) (Goal.imp (encode ψ) (encode ψ))) := by
  have hBody : Derives (encode ψ :: encode φ :: P) (encode ψ) := by
    exact derives_mono_program
      (P := encode ψ :: P)
      (Q := encode ψ :: encode φ :: P)
      (g := encode ψ)
      (by
        intro x hx
        simp at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hx))
      (ihψ P)
  exact Derives.imp (Derives.imp hBody)

theorem search_cps_conj_right_cont_of_self_support
    (φ ψ : IPL)
    (ihψ : ∀ Q : Program, SearchSupports (encode ψ :: Q) (encode ψ))
    (P : Program) :
    SearchSupports P (Goal.imp (encode φ) (Goal.imp (encode ψ) (encode ψ))) := by
  exact derives_iff_searchSupports.mp <|
    derives_cps_conj_right_cont_of_self_support φ ψ
      (fun Q => derives_iff_searchSupports.mpr (ihψ Q))
      P

/--
If the continuation goal `h` is derivable, then the CPS conjunction body
instantiated at `h` is derivable as well.
-/
theorem derives_substGoalWithGoal_encode_conj_body_of_derived
    {P : Program} {φ ψ : IPL} {h : Goal} :
    Derives P h →
      Derives P
        (substGoalWithGoal
          (Goal.imp
            (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
            (Goal.atom (.bvar 0)))
          0 h) := by
  intro hh
  rw [substGoalWithGoal_encode_conj_body]
  exact derives_imp_of_derived (g := Goal.imp (encode φ) (Goal.imp (encode ψ) h)) hh

theorem search_substGoalWithGoal_encode_conj_body_of_search
    {P : Program} {φ ψ : IPL} {h : Goal} :
    SearchSupports P h →
      SearchSupports P
        (substGoalWithGoal
          (Goal.imp
            (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
            (Goal.atom (.bvar 0)))
          0 h) := by
  intro hh
  exact derives_iff_searchSupports.mp <|
    derives_substGoalWithGoal_encode_conj_body_of_derived
      (φ := φ) (ψ := ψ) (h := h) (derives_iff_searchSupports.mpr hh)

/--
If the continuation goal `h` is derivable, then the CPS disjunction body
instantiated at `h` is derivable as well.
-/
theorem derives_substGoalWithGoal_encode_disj_body_of_derived
    {P : Program} {φ ψ : IPL} {h : Goal} :
    Derives P h →
      Derives P
        (substGoalWithGoal
          (Goal.imp
            (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
            (Goal.imp
              (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
              (Goal.atom (.bvar 0))))
          0 h) := by
  intro hh
  rw [substGoalWithGoal_encode_disj_body]
  exact derives_imp_of_derived
    (g := Goal.imp (encode φ) h)
    (derives_imp_of_derived (g := Goal.imp (encode ψ) h) hh)

theorem search_substGoalWithGoal_encode_disj_body_of_search
    {P : Program} {φ ψ : IPL} {h : Goal} :
    SearchSupports P h →
      SearchSupports P
        (substGoalWithGoal
          (Goal.imp
            (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
            (Goal.imp
              (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
              (Goal.atom (.bvar 0))))
          0 h) := by
  intro hh
  exact derives_iff_searchSupports.mp <|
    derives_substGoalWithGoal_encode_disj_body_of_derived
      (φ := φ) (ψ := ψ) (h := h) (derives_iff_searchSupports.mpr hh)

/--
If a program derives `∀X.X`, then it derives every encoded IPL formula.

This is the precise base case of the remaining mixed transport recursion:
the ambient universal body `X` is not an obstruction at all. Once `∀X.X`
is derivable, the program already supports every CPS encoding directly.
-/
theorem derives_encode_of_derived_all_top {P : Program} :
    Derives P (.all (.atom (.bvar 0))) → ∀ φ : IPL, Derives P (encode φ) := by
  intro hTop
  have hAtom : ∀ a : Atom, Derives P (.atom (.atom a)) := by
    intro a
    have hHead : Derives (.all (.atom (.bvar 0)) :: P) (.atom (.atom a)) := by
      apply Derives.atom
      exact DerivesFromAny.here <| by
        simpa [substGoal] using
          (Fires.allAtom
            (P := .all (.atom (.bvar 0)) :: P)
            (g := .atom (.bvar 0))
            a
            Fires.atom)
    exact derives_cut hTop hHead
  intro φ
  induction φ with
  | atom a =>
      simpa [encode] using hAtom a
  | bot =>
      simpa [encode] using hTop
  | conj φ ψ ihφ ihψ =>
      let c := freshAtomForGoal P
        (Goal.imp
          (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
          (Goal.atom (.bvar 0)))
      refine Derives.all c ?_ ?_ ?_
      · exact
          (freshAtomForGoal_fresh P
            (Goal.imp
              (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
              (Goal.atom (.bvar 0)))).1
      · exact
          (freshAtomForGoal_fresh P
            (Goal.imp
              (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
              (Goal.atom (.bvar 0)))).2
      · exact derives_imp_of_derived (g := substGoal
          (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
          0 c) (hAtom c)
  | disj φ ψ ihφ ihψ =>
      let c := freshAtomForGoal P
        (Goal.imp
          (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
          (Goal.imp
            (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
            (Goal.atom (.bvar 0))))
      refine Derives.all c ?_ ?_ ?_
      · exact
          (freshAtomForGoal_fresh P
            (Goal.imp
              (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
              (Goal.imp
                (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
                (Goal.atom (.bvar 0))))).1
      · exact
          (freshAtomForGoal_fresh P
            (Goal.imp
              (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
              (Goal.imp
                (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
                (Goal.atom (.bvar 0))))).2
      · exact derives_imp_of_derived
          (g := substGoal (Goal.imp (encode φ) (Goal.atom (.bvar 0))) 0 c)
          (derives_imp_of_derived
            (g := substGoal (Goal.imp (encode ψ) (Goal.atom (.bvar 0))) 0 c)
            (hAtom c))
  | imp φ ψ ihφ ihψ =>
      exact derives_imp_of_derived (g := encode φ) ihψ

theorem search_encode_of_derived_all_top {P : Program} :
    Derives P (.all (.atom (.bvar 0))) → ∀ φ : IPL, SearchSupports P (encode φ) := by
  intro hTop φ
  exact derives_iff_searchSupports.mp <|
    derives_encode_of_derived_all_top hTop φ

/--
If `∀X.X` is already a member of the ambient program, then every encoded IPL
formula searches from that program.

This packages the new `derived_all_top` theorem into the exact membership form
that can arise in the remaining conjunction ambient-`.all` branch.
-/
theorem search_encode_of_all_top_member {P : Program}
    (hTopMem : .all (.atom (.bvar 0)) ∈ P) :
    ∀ φ : IPL, SearchSupports P (encode φ) := by
  let D : Goal := .all (.atom (.bvar 0))
  have hMemeq : ∀ x, x ∈ D :: P ↔ x ∈ P := by
    intro x
    constructor
    · intro hx
      simp [D, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hTopMem
      · exact hx
    · intro hx
      by_cases hEq : x = D
      · subst hEq
        simp [D, List.mem_cons]
      · simp [D, List.mem_cons, hEq, hx]
  have hTopHead : Derives (D :: P) D := by
    let c := freshAtomForGoal (D :: P) (.atom (.bvar 0))
    refine Derives.all c ?_ ?_ ?_
    · exact (freshAtomForGoal_fresh (D :: P) (.atom (.bvar 0))).1
    · exact (freshAtomForGoal_fresh (D :: P) (.atom (.bvar 0))).2
    · apply Derives.atom
      exact DerivesFromAny.here <| by
        simpa [D, substGoal] using
          (Fires.allAtom (P := D :: P) (g := .atom (.bvar 0)) c Fires.atom)
  have hTop : Derives P D := by
    exact derives_of_program_memeq hMemeq hTopHead
  intro φ
  exact search_encode_of_derived_all_top hTop φ

/--
If an ambient member `∀X.(prem -> X)` is available and the corresponding fresh
instantiated premise is derivable, then the same program already derives
`∀X.X`.

This is the clause-local collapse used by the conjunction follow-on: once the
instantiated premise has been transported to a genuinely fresh witness, the
ambient top-tail clause is enough to recover the universal top directly.
-/
private theorem derives_all_top_of_all_imp_top_member_instantiated
    {P : Program} {prem : Goal} {c : Atom}
    (hDP : Goal.all (.imp prem (.atom (.bvar 0))) ∈ P)
    (hcP : c ∉ programAtoms P)
    (hPrem : Derives P (substGoal prem 0 c)) :
    Derives P (.all (.atom (.bvar 0))) := by
  have hAtom : Derives P (.atom (.atom c)) := by
    apply Derives.atom
    exact derivesFromAny_of_mem hDP <| by
      simpa [substGoal] using
        (Fires.allAtom (P := P) (g := .imp prem (.atom (.bvar 0))) c
          (Fires.imp hPrem Fires.atom))
  exact Derives.all c hcP (by simp [goalAtoms, atomVarAtoms]) hAtom

-- Program monotonicity and weakening are now proved in `Contextual.Derives`
-- via mutual Bool-level equivariance on `search`/`searchAnyAssumption`/`fires`.

-- Note: search_strengthen (removing irrelevant clauses) is NOT stated as a
-- general axiom because it's false in general. For specific cases (e.g.,
-- removing clauses that only fire for fresh atoms), it follows from the
-- paper's substitution lemma (Lemma 4.5) + self-support (Lemma 4.4).

-- ============================================================
-- § 3. Base monotonicity
-- ============================================================

/-- With Base = Program and encodeBase = id, base monotonicity is just
    the BaseExtends premise itself. -/
theorem encodeBase_mono {B C : Base} (h : BaseExtends B C) :
    ∀ x, x ∈ encodeBase B → x ∈ encodeBase C := by
  intro x hx
  exact h hx

-- ============================================================
-- § 4. Phase 3 head self-support base cases
-- ============================================================

/--
Encoded atoms support themselves when added as a program head.

This is the atom base-case of the Phase 3 encoded-head self-support family.
-/
theorem derives_self_support_encode_head_atom (P : Program) (a : Atom) :
    Derives (encode (.atom a) :: P) (encode (.atom a)) := by
  simpa [encode] using
    (derives_self_support_atom (P := encode (.atom a) :: P) (a := .atom a) (by simp [encode]))

/--
Encoded bottom supports itself when added as a program head.

Unlike the atom case, this uses the `.all` introduction rule directly: the head
`encode .bot = ∀X.X` can always fire the chosen fresh atom witness.
-/
theorem derives_self_support_encode_head_bot (P : Program) :
    Derives (encode .bot :: P) (encode .bot) := by
  let c := freshAtomForGoal (encode .bot :: P) (.atom (.bvar 0))
  refine Derives.all c ?_ ?_ ?_
  · exact (freshAtomForGoal_fresh (encode .bot :: P) (.atom (.bvar 0))).1
  · exact (freshAtomForGoal_fresh (encode .bot :: P) (.atom (.bvar 0))).2
  · apply Derives.atom
    apply DerivesFromAny.here
    simpa [encode, c, substGoal] using
      (Fires.allAtom (P := encode .bot :: P) (g := .atom (.bvar 0)) c Fires.atom)

theorem search_self_support_encode_head_atom (P : Program) (a : Atom) :
    SearchSupports (encode (.atom a) :: P) (encode (.atom a)) :=
  derives_iff_searchSupports.mp (derives_self_support_encode_head_atom P a)

theorem search_self_support_encode_head_bot (P : Program) :
    SearchSupports (encode .bot :: P) (encode .bot) :=
  derives_iff_searchSupports.mp (derives_self_support_encode_head_bot P)

/--
If both conjunct encodings already satisfy head self-support on arbitrary ambient
programs, then the encoded conjunction head does too.

This is the direct structural construction for the conjunction CPS head. It
isolates the remaining real blocker cleanly: only the recursive self-support
premises for subformulas are left open.
-/
theorem derives_self_support_encode_head_conj_of
    (φ ψ : IPL)
    (ihφ : ∀ Q : Program, Derives (encode φ :: Q) (encode φ))
    (ihψ : ∀ Q : Program, Derives (encode ψ :: Q) (encode ψ))
    (P : Program) :
    Derives (encode (.conj φ ψ) :: P) (encode (.conj φ ψ)) := by
  let c := freshAtomForGoal (encode (.conj φ ψ) :: P)
    (Goal.imp
      (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
      (Goal.atom (.bvar 0)))
  let K : Goal :=
    substGoal
      (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
      0 c
  refine Derives.all c ?_ ?_ ?_
  · exact
      (freshAtomForGoal_fresh (encode (.conj φ ψ) :: P)
        (Goal.imp
          (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
          (Goal.atom (.bvar 0)))).1
  · exact
      (freshAtomForGoal_fresh (encode (.conj φ ψ) :: P)
        (Goal.imp
          (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (.bvar 0))))
          (Goal.atom (.bvar 0)))).2
  · apply Derives.imp
    apply Derives.atom
    apply DerivesFromAny.there
    apply DerivesFromAny.here
    apply Fires.allAtom c
    simp [encode, c]
    apply Fires.imp
    · apply Derives.imp
      apply Derives.imp
      apply Derives.atom
      apply DerivesFromAny.there
      apply DerivesFromAny.there
      apply DerivesFromAny.here
      apply Fires.imp
      · simpa [K, substGoal_encode] using
          (derives_weaken (extras := [encode ψ]) <|
            ihφ (K :: encode (.conj φ ψ) :: P))
      · apply Fires.imp
        · simpa [K, substGoal_encode] using
            ihψ (encode φ :: K :: encode (.conj φ ψ) :: P)
        · exact Fires.atom
    · exact Fires.atom

theorem search_self_support_encode_head_conj_of
    (φ ψ : IPL)
    (ihφ : ∀ Q : Program, SearchSupports (encode φ :: Q) (encode φ))
    (ihψ : ∀ Q : Program, SearchSupports (encode ψ :: Q) (encode ψ))
    (P : Program) :
    SearchSupports (encode (.conj φ ψ) :: P) (encode (.conj φ ψ)) := by
  exact derives_iff_searchSupports.mp <|
    derives_self_support_encode_head_conj_of φ ψ
      (fun Q => derives_iff_searchSupports.mpr (ihφ Q))
      (fun Q => derives_iff_searchSupports.mpr (ihψ Q))
      P

/--
If both disjunct encodings already satisfy head self-support on arbitrary ambient
programs, then the encoded disjunction head does too.
-/
theorem derives_self_support_encode_head_disj_of
    (φ ψ : IPL)
    (ihφ : ∀ Q : Program, Derives (encode φ :: Q) (encode φ))
    (ihψ : ∀ Q : Program, Derives (encode ψ :: Q) (encode ψ))
    (P : Program) :
    Derives (encode (.disj φ ψ) :: P) (encode (.disj φ ψ)) := by
  let c := freshAtomForGoal (encode (.disj φ ψ) :: P)
    (Goal.imp
      (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
      (Goal.imp
        (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
        (Goal.atom (.bvar 0))))
  let Kφ : Goal := substGoal (Goal.imp (encode φ) (Goal.atom (.bvar 0))) 0 c
  let Kψ : Goal := substGoal (Goal.imp (encode ψ) (Goal.atom (.bvar 0))) 0 c
  refine Derives.all c ?_ ?_ ?_
  · exact
      (freshAtomForGoal_fresh (encode (.disj φ ψ) :: P)
        (Goal.imp
          (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
          (Goal.imp
            (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
            (Goal.atom (.bvar 0))))).1
  · exact
      (freshAtomForGoal_fresh (encode (.disj φ ψ) :: P)
        (Goal.imp
          (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
          (Goal.imp
            (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
            (Goal.atom (.bvar 0))))).2
  · apply Derives.imp
    apply Derives.imp
    apply Derives.atom
    apply DerivesFromAny.there
    apply DerivesFromAny.there
    apply DerivesFromAny.here
    apply Fires.allAtom c
    simp [encode, c]
    apply Fires.imp
    · apply Derives.imp
      apply Derives.atom
      apply DerivesFromAny.there
      apply DerivesFromAny.there
      apply DerivesFromAny.here
      apply Fires.imp
      · simpa [Kφ, Kψ, substGoal_encode] using
          ihφ (Kψ :: Kφ :: encode (.disj φ ψ) :: P)
      · exact Fires.atom
    · apply Fires.imp
      · apply Derives.imp
        apply Derives.atom
        apply DerivesFromAny.there
        apply DerivesFromAny.here
        apply Fires.imp
        · simpa [Kφ, Kψ, substGoal_encode] using
            ihψ (Kψ :: Kφ :: encode (.disj φ ψ) :: P)
        · exact Fires.atom
      · exact Fires.atom

theorem search_self_support_encode_head_disj_of
    (φ ψ : IPL)
    (ihφ : ∀ Q : Program, SearchSupports (encode φ :: Q) (encode φ))
    (ihψ : ∀ Q : Program, SearchSupports (encode ψ :: Q) (encode ψ))
    (P : Program) :
    SearchSupports (encode (.disj φ ψ) :: P) (encode (.disj φ ψ)) := by
  exact derives_iff_searchSupports.mp <|
    derives_self_support_encode_head_disj_of φ ψ
      (fun Q => derives_iff_searchSupports.mpr (ihφ Q))
      (fun Q => derives_iff_searchSupports.mpr (ihψ Q))
      P

-- ============================================================
-- § 5. Atomic base lemmas
-- ============================================================

-- Helper: fires on an atom goal checks equality
theorem fires_atom_eq (fuel : Nat) (P : Program) (v₁ v₂ : AtomVar) :
    fires (fuel + 1) P (.atom v₁) v₂ = decide (v₁ = v₂) := by
  simp [fires]

-- Helper: searchAnyAssumption iteration on atom goals with a fixed program
private theorem searchAnyAssumption_atom_list (fuel : Nat) (P : Program)
    (atoms : List Atom) (a : Atom) :
    searchAnyAssumption (fuel + 1) P (atoms.map fun b => Goal.atom (.atom b)) (.atom a) = true
      ↔ a ∈ atoms := by
  induction atoms with
  | nil => simp [searchAnyAssumption]
  | cons hd tl ih =>
      simp only [List.map_cons, searchAnyAssumption, fires_atom_eq, Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · simp at h; simp [h]
        · exact List.mem_cons_of_mem _ (ih.mp h)
      · intro hmem
        simp [List.mem_cons] at hmem
        rcases hmem with rfl | h
        · exact Or.inl (by simp)
        · exact Or.inr (ih.mpr h)

private theorem searchAnyAssumption_atom_list_program_irrelevant
    (fuel : Nat) (P P' : Program) (atoms : List Atom) (a : Atom) :
    searchAnyAssumption fuel P (atoms.map fun b => Goal.atom (.atom b)) (.atom a) =
      searchAnyAssumption fuel P' (atoms.map fun b => Goal.atom (.atom b)) (.atom a) := by
  induction atoms generalizing fuel with
  | nil =>
      simp [searchAnyAssumption]
  | cons b rest ih =>
      cases fuel with
      | zero =>
          simp [searchAnyAssumption, fires, ih]
      | succ fuel =>
          simp [searchAnyAssumption, fires, ih]

-- Corollary when P = the atom list itself
private theorem searchAnyAssumption_encodeBase (fuel : Nat) (atoms : List Atom) (a : Atom) :
    let P := atoms.map fun b => Goal.atom (.atom b)
    searchAnyAssumption (fuel + 1) P P (.atom a) = true ↔ a ∈ atoms :=
  searchAnyAssumption_atom_list fuel _ atoms a

/--
For an atomic base, atom a is searchable in atomicBase atoms iff a ∈ atoms.
-/
theorem atomicBase_search_atom_iff (atoms : List Atom) (a : Atom) :
    SearchSupports (atomicBase atoms) (Goal.atom (.atom a)) ↔ a ∈ atoms := by
  unfold SearchSupports
  have henc : atomicBase atoms = atoms.map (fun b => Goal.atom (.atom b)) := rfl
  constructor
  · rintro ⟨fuel, hfuel⟩
    cases fuel with
    | zero => simp [search] at hfuel
    | succ fuel =>
        cases fuel with
        | zero =>
            simp [search] at hfuel
            rw [henc] at hfuel
            let P := atoms.map fun b => Goal.atom (.atom b)
            have hzero : ∀ (gs : List Goal),
                searchAnyAssumption 0 P gs (.atom a) = false := by
              intro gs
              induction gs with
              | nil => simp [searchAnyAssumption]
              | cons g rest ih => simp [searchAnyAssumption, fires, ih]
            rw [hzero P] at hfuel
            exact absurd hfuel (by decide)
        | succ fuel =>
            simp [search] at hfuel
            rw [henc] at hfuel
            exact (searchAnyAssumption_encodeBase fuel atoms a).mp hfuel
  · intro hmem
    refine ⟨2, ?_⟩
    simp [search]
    rw [henc]
    exact (searchAnyAssumption_encodeBase 0 atoms a).mpr hmem

-- Legacy alias for backward compatibility
theorem encodeBase_search_atom_iff (atoms : List Atom) (a : Atom) :
    SearchSupports (atomicBase atoms) (Goal.atom (.atom a)) ↔ a ∈ atoms :=
  atomicBase_search_atom_iff atoms a

theorem atomicBase_search_fresh_atom_false (fuel : Nat) (atoms : List Atom) (a : Atom)
    (ha : a ∉ atoms) :
    search fuel (atomicBase atoms) (.atom (.atom a)) = false := by
  cases fuel with
  | zero =>
      simp [search]
  | succ fuel =>
      by_cases hsearch : searchAnyAssumption fuel (atomicBase atoms) (atomicBase atoms) (.atom a) = true
      · have hsupp : SearchSupports (atomicBase atoms) (.atom (.atom a)) := by
          exact ⟨fuel + 1, by simpa [search] using hsearch⟩
        exact False.elim (ha ((atomicBase_search_atom_iff atoms a).mp hsupp))
      · simp [search, hsearch]

private theorem atomicBase_atom_head_memeq (atoms : List Atom) (a : Atom)
    (ha : a ∈ atoms) :
    ∀ x, x ∈ Goal.atom (.atom a) :: atomicBase atoms ↔ x ∈ atomicBase atoms := by
  intro x
  constructor
  · intro hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact by
        simp only [atomicBase, List.mem_map]
        exact ⟨a, ha, rfl⟩
    · exact hx
  · intro hx
    exact List.mem_cons_of_mem _ hx

theorem search_cut_atom (atoms : List Atom) (a : Atom) (ψ : IPL) :
    SearchSupports (atomicBase atoms) (encode (.atom a)) →
    SearchSupports (encode (.atom a) :: atomicBase atoms) (encode ψ) →
    SearchSupports (atomicBase atoms) (encode ψ) := by
  intro hAtom hψ
  have ha : a ∈ atoms := (atomicBase_search_atom_iff atoms a).mp hAtom
  exact searchSupports_of_program_memeq (atomicBase_atom_head_memeq atoms a ha) hψ

theorem searchAnyAssumption_atomicBase_fresh_atom_from_head {fuel : Nat} {atoms : List Atom}
    {K : Goal} {a : Atom} (ha : a ∉ atoms) :
    searchAnyAssumption fuel (K :: atomicBase atoms) (K :: atomicBase atoms) (.atom a) = true →
      fires fuel (K :: atomicBase atoms) K (.atom a) = true := by
  have htailEq :
      searchAnyAssumption fuel (K :: atomicBase atoms) (atomicBase atoms) (.atom a) =
        searchAnyAssumption fuel (atomicBase atoms) (atomicBase atoms) (.atom a) := by
    simpa [atomicBase] using
      searchAnyAssumption_atom_list_program_irrelevant fuel (K :: atomicBase atoms) (atomicBase atoms) atoms a
  have htailFalse :
      searchAnyAssumption fuel (K :: atomicBase atoms) (atomicBase atoms) (.atom a) = false := by
    rw [htailEq]
    have hsearchFalse := atomicBase_search_fresh_atom_false (fuel + 1) atoms a ha
    simpa [search] using hsearchFalse
  intro h
  simp [searchAnyAssumption, Bool.or_eq_true] at h
  rcases h with hK | hTail
  · exact hK
  · exact False.elim (by rw [htailFalse] at hTail; cases hTail)

-- Legacy alias
theorem searchAnyAssumption_encodeBase_fresh_atom_from_head {fuel : Nat} {atoms : List Atom}
    {K : Goal} {a : Atom} (ha : a ∉ atoms) :
    searchAnyAssumption fuel (K :: atomicBase atoms) (K :: atomicBase atoms) (.atom a) = true →
      fires fuel (K :: atomicBase atoms) K (.atom a) = true :=
  searchAnyAssumption_atomicBase_fresh_atom_from_head ha

theorem searchAnyAssumption_atomicBase_fresh_atom_from_two_heads {fuel : Nat} {atoms : List Atom}
    {Kφ Kψ : Goal} {a : Atom} (ha : a ∉ atoms) :
    searchAnyAssumption fuel (Kψ :: Kφ :: atomicBase atoms) (Kψ :: Kφ :: atomicBase atoms) (.atom a) = true →
      fires fuel (Kψ :: Kφ :: atomicBase atoms) Kψ (.atom a) = true ∨
        fires fuel (Kψ :: Kφ :: atomicBase atoms) Kφ (.atom a) = true := by
  intro h
  simp [searchAnyAssumption, Bool.or_eq_true] at h
  rcases h with hKψ | hTail
  · exact Or.inl hKψ
  · have htailEq :
        searchAnyAssumption fuel (Kψ :: Kφ :: atomicBase atoms) (atomicBase atoms) (.atom a) =
          searchAnyAssumption fuel (atomicBase atoms) (atomicBase atoms) (.atom a) := by
      simpa [atomicBase] using
        searchAnyAssumption_atom_list_program_irrelevant fuel
          (Kψ :: Kφ :: atomicBase atoms) (atomicBase atoms) atoms a
    have htailFalse :
        searchAnyAssumption fuel (Kψ :: Kφ :: atomicBase atoms) (atomicBase atoms) (.atom a) = false := by
      rw [htailEq]
      have hsearchFalse := atomicBase_search_fresh_atom_false (fuel + 1) atoms a ha
      simpa [search] using hsearchFalse
    rcases hTail with hKφ | hBase
    · exact Or.inr hKφ
    · exact False.elim (by rw [htailFalse] at hBase; cases hBase)

-- Legacy alias
theorem searchAnyAssumption_encodeBase_fresh_atom_from_two_heads {fuel : Nat} {atoms : List Atom}
    {Kφ Kψ : Goal} {a : Atom} (ha : a ∉ atoms) :
    searchAnyAssumption fuel (Kψ :: Kφ :: atomicBase atoms) (Kψ :: Kφ :: atomicBase atoms) (.atom a) = true →
      fires fuel (Kψ :: Kφ :: atomicBase atoms) Kψ (.atom a) = true ∨
        fires fuel (Kψ :: Kφ :: atomicBase atoms) Kφ (.atom a) = true :=
  searchAnyAssumption_atomicBase_fresh_atom_from_two_heads ha

/--
Bottom (⊥) is never supported: encode .bot = ∀X. X requires proving a fresh atom,
which no atomic base can supply.
-/
-- programAtoms of an atomic-encoded base equals the original atoms
private theorem programAtoms_encodeBase_list (atoms : List Atom) :
    programAtoms (atoms.map fun a => Goal.atom (.atom a)) = atoms := by
  induction atoms with
  | nil => rfl
  | cons hd tl ih =>
      show goalAtoms (Goal.atom (.atom hd)) ++ programAtoms (tl.map fun a => Goal.atom (.atom a)) = hd :: tl
      simp only [goalAtoms, atomVarAtoms, List.singleton_append]
      exact congrArg (List.cons hd) ih

theorem programAtoms_atomicBase (atoms : List Atom) :
    programAtoms (atomicBase atoms) = atoms :=
  programAtoms_encodeBase_list atoms

-- Legacy alias
theorem programAtoms_encodeBase (atoms : List Atom) :
    programAtoms (atomicBase atoms) = atoms :=
  programAtoms_atomicBase atoms

-- The fresh atom for atomicBase atoms is not in atoms
private theorem le_maxAtomId_of_mem' {atoms : List Atom} {a : Atom} (h : a ∈ atoms) :
    a.id ≤ maxAtomId atoms := by
  induction atoms with
  | nil => cases h
  | cons hd tl ih =>
      simp [maxAtomId]
      rcases List.mem_cons.mp h with rfl | htl
      · exact Nat.le_max_left _ _
      · exact le_trans (ih htl) (Nat.le_max_right _ _)

private theorem fresh_not_mem (atoms : List Atom) :
    ({ id := maxAtomId atoms + 1 } : Atom) ∉ atoms := by
  intro hmem
  have hle := le_maxAtomId_of_mem' hmem
  exact Nat.not_succ_le_self _ (by simpa using hle)

theorem freshAtomForGoal_not_in_atomicBase (atoms : List Atom) (g : Goal) :
    (freshAtomForGoal (atomicBase atoms) g) ∉ atoms := by
  intro hmem
  have hmem' : freshAtomForGoal (atomicBase atoms) g ∈ programAtoms (atomicBase atoms) := by
    rwa [programAtoms_atomicBase]
  exact fresh_not_mem (programAtoms (atomicBase atoms) ++ goalAtoms g)
    (List.mem_append_left _ hmem')

-- Legacy alias
theorem freshAtomForGoal_not_in_base (atoms : List Atom) (g : Goal) :
    (freshAtomForGoal (atomicBase atoms) g) ∉ atoms :=
  freshAtomForGoal_not_in_atomicBase atoms g

private theorem cps_conj_K_fires_only_for
    {P : Program} {φ ψ : IPL} {a : Atom} {v : AtomVar}
    (hF : Fires P (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))) v) :
    v = .atom a := by
  cases hF with
  | imp hφ hRest =>
      cases hRest with
      | imp hψ hAtom =>
          cases hAtom
          rfl

private theorem cps_conj_left_from_head
    {P : Program} {φ ψ : IPL} {a : Atom}
    (hF : Fires P (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))) (.atom a)) :
    Derives P (encode φ) := by
  cases hF with
  | imp hφ hRest =>
      exact hφ

private theorem cps_conj_right_from_head
    {P : Program} {φ ψ : IPL} {a : Atom}
    (hF : Fires P (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))) (.atom a)) :
    Derives P (encode ψ) := by
  cases hF with
  | imp hφ hRest =>
      cases hRest with
      | imp hψ hAtom =>
          exact hψ

private theorem cps_conj_atom_from_sub
    {P : Program} {φ ψ : IPL} {a : Atom}
    (h : Derives P (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
        (.atom (.atom a)))) :
    Derives (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P) (.atom (.atom a)) := by
  cases h with
  | imp hAtom =>
      exact hAtom

private theorem cps_conj_derives_from_fresh_body
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeφ : a ∉ goalAtoms (encode φ))
    (haEncodeψ : a ∉ goalAtoms (encode ψ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a)))) :
    Derives P (encode (.conj φ ψ)) := by
  refine Derives.all a haP ?_ ?_
  · simpa [encode, goalAtoms, atomVarAtoms] using
      show a ∉ goalAtoms (encode φ) ++ goalAtoms (encode ψ) from
        by
          intro hm
          rcases List.mem_append.mp hm with hm | hm
          · exact haEncodeφ hm
          · exact haEncodeψ hm
  · simpa [encode, substGoal, substGoal_encode] using hSub

private theorem cps_conj_head_context_derives_to_ambient_search
    {P : Program} {φ ψ χ : IPL} {a : Atom}
    (haEncodeχ : a ∉ goalAtoms (encode χ))
    (haP : a ∉ programAtoms P)
    (hDer :
      Derives
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (encode χ)) :
    SearchSupports P (encode χ) := by
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  rcases derives_to_search hDer with ⟨fuelχ, hfuelχ⟩
  exact
    ⟨fuelχ,
      search_strengthen_fresh_head
        (haK := by simp [goalAtoms, atomVarAtoms])
        (hK_fires_only_a := by
          intro P' v hF
          exact cps_conj_K_fires_only_for (φ := φ) (ψ := ψ) (a := a) hF)
        fuelχ P (encode χ) haEncodeχ haP hfuelχ⟩

private theorem derives_to_headGoalSupportsCtx_singleton
    {P : Program} {K g : Goal}
    (hDer : Derives (K :: P) g) :
    HeadGoalSupportsCtx [K] P g := by
  rw [headGoalSupportsCtx_iff_searchCtx]
  simpa [encodeBase] using (derives_iff_searchSupports.mp hDer)

private theorem fires_imp_to_headGoalSupportsCtx_and_headGoalFires
    {P : Program} {K g₁ g₂ : Goal} {a : Atom} {fuel : Nat}
    (hFireD : fires fuel (K :: P) (.imp g₁ g₂) (.atom a) = true) :
    HeadGoalSupportsCtx [K] P g₁ ∧
      HeadGoalFiresCtx [K] P g₂ (.atom a) := by
  have hFire : Fires (K :: P) (.imp g₁ g₂) (.atom a) := by
    simpa using fires_to_derives hFireD
  exact
    match hFire with
    | .imp hPrem hTail =>
        ⟨derives_to_headGoalSupportsCtx_singleton hPrem, by
          rw [headGoalFiresCtx_iff_firesCtx]
          simpa [encodeBase] using hTail⟩

/--
Swap the fresh witness used by an instantiated premise while moving between the
corresponding conjunction head contexts.

This is the honest transport supported by relabeling: the continuation head and
the instantiated body move together from witness `a` to witness `c`.
-/
private theorem cps_conj_head_context_substGoal_witness_swap
    {P : Program} {φ ψ : IPL} {prem : Goal} {a c : Atom}
    (haP : a ∉ programAtoms P)
    (hcP : c ∉ programAtoms P)
    (haEncodeφ : a ∉ goalAtoms (encode φ))
    (hcEncodeφ : c ∉ goalAtoms (encode φ))
    (haEncodeψ : a ∉ goalAtoms (encode ψ))
    (hcEncodeψ : c ∉ goalAtoms (encode ψ))
    (haPrem : a ∉ goalAtoms prem)
    (hcPrem : c ∉ goalAtoms prem)
    (hDer :
      Derives
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (substGoal prem 0 a)) :
    Derives
      (.imp (encode φ) (.imp (encode ψ) (.atom (.atom c))) :: P)
      (substGoal prem 0 c) := by
  let τ : Atom → Atom := swapAtoms a c
  have hτP : relabelProgram τ P = P :=
    swapAtoms_program_id_of_fresh haP hcP
  have hτPMap : List.map (relabelGoal τ) P = P := by
    simpa [relabelProgram] using hτP
  have hτφ : relabelGoal τ (encode φ) = encode φ :=
    swapAtoms_goal_id_of_fresh haEncodeφ hcEncodeφ
  have hτψ : relabelGoal τ (encode ψ) = encode ψ :=
    swapAtoms_goal_id_of_fresh haEncodeψ hcEncodeψ
  have hτPrem : relabelGoal τ prem = prem :=
    swapAtoms_goal_id_of_fresh haPrem hcPrem
  have hτHead :
      relabelGoal τ (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))) =
        .imp (encode φ) (.imp (encode ψ) (.atom (.atom c))) := by
    simp only [relabelGoal, hτφ, hτψ, relabelAtomVar]
    simp [τ, swapAtoms_self_left]
  have hτCtx :
      relabelProgram τ
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P) =
        .imp (encode φ) (.imp (encode ψ) (.atom (.atom c))) :: P := by
    simp [relabelProgram, hτHead, hτPMap]
  have hRel := derives_relabel (swapAtoms_injective a c) hDer
  simpa [hτCtx, hτPrem, τ,
    relabelGoal_substGoal_comm, relabelAtomVar, swapAtoms_self_left] using hRel

/--
Fire-side witness transport for the conjunction head context.

As above, the continuation head and the instantiated body move together from
`a` to `c`.
-/
private theorem cps_conj_head_context_fire_witness_swap
    {P : Program} {φ ψ : IPL} {prem : Goal} {a c : Atom}
    (haP : a ∉ programAtoms P)
    (hcP : c ∉ programAtoms P)
    (haEncodeφ : a ∉ goalAtoms (encode φ))
    (hcEncodeφ : c ∉ goalAtoms (encode φ))
    (haEncodeψ : a ∉ goalAtoms (encode ψ))
    (hcEncodeψ : c ∉ goalAtoms (encode ψ))
    (haPrem : a ∉ goalAtoms prem)
    (hcPrem : c ∉ goalAtoms prem)
    (hFire :
      Fires
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (substGoal prem 0 a)
        (.atom a)) :
    Fires
      (.imp (encode φ) (.imp (encode ψ) (.atom (.atom c))) :: P)
      (substGoal prem 0 c)
      (.atom c) := by
  let τ : Atom → Atom := swapAtoms a c
  have hτP : relabelProgram τ P = P :=
    swapAtoms_program_id_of_fresh haP hcP
  have hτPMap : List.map (relabelGoal τ) P = P := by
    simpa [relabelProgram] using hτP
  have hτφ : relabelGoal τ (encode φ) = encode φ :=
    swapAtoms_goal_id_of_fresh haEncodeφ hcEncodeφ
  have hτψ : relabelGoal τ (encode ψ) = encode ψ :=
    swapAtoms_goal_id_of_fresh haEncodeψ hcEncodeψ
  have hτPrem : relabelGoal τ prem = prem :=
    swapAtoms_goal_id_of_fresh haPrem hcPrem
  have hτHead :
      relabelGoal τ (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))) =
        .imp (encode φ) (.imp (encode ψ) (.atom (.atom c))) := by
    simp only [relabelGoal, hτφ, hτψ, relabelAtomVar]
    simp [τ, swapAtoms_self_left]
  have hτCtx :
      relabelProgram τ
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P) =
        .imp (encode φ) (.imp (encode ψ) (.atom (.atom c))) :: P := by
    simp [relabelProgram, hτHead, hτPMap]
  have hRel := fires_relabel (swapAtoms_injective a c) hFire
  simpa [hτCtx, hτPrem, τ,
    relabelGoal_substGoal_comm, relabelAtomVar, swapAtoms_self_left] using hRel

/--
Stable-conclusion witness transport for the conjunction head context.

If the conclusion goal itself avoids both witnesses, then moving the
continuation head from `a` to `c` preserves derivability of that stable goal.
-/
private theorem cps_conj_head_context_goal_witness_swap
    {P : Program} {φ ψ : IPL} {g : Goal} {a c : Atom}
    (haP : a ∉ programAtoms P)
    (hcP : c ∉ programAtoms P)
    (haEncodeφ : a ∉ goalAtoms (encode φ))
    (hcEncodeφ : c ∉ goalAtoms (encode φ))
    (haEncodeψ : a ∉ goalAtoms (encode ψ))
    (hcEncodeψ : c ∉ goalAtoms (encode ψ))
    (haG : a ∉ goalAtoms g)
    (hcG : c ∉ goalAtoms g)
    (hDer :
      Derives
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        g) :
    Derives
      (.imp (encode φ) (.imp (encode ψ) (.atom (.atom c))) :: P)
      g := by
  let τ : Atom → Atom := swapAtoms a c
  have hτP : relabelProgram τ P = P :=
    swapAtoms_program_id_of_fresh haP hcP
  have hτPMap : List.map (relabelGoal τ) P = P := by
    simpa [relabelProgram] using hτP
  have hτφ : relabelGoal τ (encode φ) = encode φ :=
    swapAtoms_goal_id_of_fresh haEncodeφ hcEncodeφ
  have hτψ : relabelGoal τ (encode ψ) = encode ψ :=
    swapAtoms_goal_id_of_fresh haEncodeψ hcEncodeψ
  have hτG : relabelGoal τ g = g :=
    swapAtoms_goal_id_of_fresh haG hcG
  have hτHead :
      relabelGoal τ (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))) =
        .imp (encode φ) (.imp (encode ψ) (.atom (.atom c))) := by
    simp only [relabelGoal, hτφ, hτψ, relabelAtomVar]
    simp [τ, swapAtoms_self_left]
  have hτCtx :
      relabelProgram τ
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P) =
        .imp (encode φ) (.imp (encode ψ) (.atom (.atom c))) :: P := by
    simp [relabelProgram, hτHead, hτPMap]
  have hRel := derives_relabel (swapAtoms_injective a c) hDer
  simpa [hτCtx, hτG, τ,
    relabelAtomVar, swapAtoms_self_left] using hRel

private theorem cps_disj_K_fires_only_for
    {P : Program} {χ : IPL} {a : Atom} {v : AtomVar}
    (hF : Fires P (.imp (encode χ) (.atom (.atom a))) v) :
    v = .atom a := by
  cases hF with
  | imp hχ hAtom =>
      cases hAtom
      rfl

private theorem cps_disj_left_from_head
    {P : Program} {φ : IPL} {a : Atom}
    (hF : Fires P (.imp (encode φ) (.atom (.atom a))) (.atom a)) :
    Derives P (encode φ) := by
  cases hF with
  | imp hφ hAtom =>
      exact hφ

private theorem cps_disj_right_from_head
    {P : Program} {ψ : IPL} {a : Atom}
    (hF : Fires P (.imp (encode ψ) (.atom (.atom a))) (.atom a)) :
    Derives P (encode ψ) := by
  cases hF with
  | imp hψ hAtom =>
      exact hψ

private theorem cps_disj_atom_from_sub
    {P : Program} {φ ψ : IPL} {a : Atom}
    (h : Derives P
      (.imp (.imp (encode φ) (.atom (.atom a)))
        (.imp (.imp (encode ψ) (.atom (.atom a))) (.atom (.atom a))))) :
    Derives
      ((.imp (encode ψ) (.atom (.atom a))) ::
        (.imp (encode φ) (.atom (.atom a))) :: P)
      (.atom (.atom a)) := by
  cases h with
  | imp hRest =>
      cases hRest with
      | imp hAtom =>
          exact hAtom

theorem cps_conj_extract_left_from_fresh_body
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeφ : a ∉ goalAtoms (encode φ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hHeadSearch :
      ∀ {fuel : Nat},
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true) :
    SearchSupports P (encode φ) := by
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have hAtom' : Derives (K :: P) (.atom (.atom a)) :=
    cps_conj_atom_from_sub hSub
  rcases derives_to_search hAtom' with ⟨fuel, hfuel⟩
  cases fuel with
  | zero =>
      simp [search] at hfuel
  | succ fuel =>
      have hHeadBool : fires fuel (K :: P) K (.atom a) = true := by
        apply hHeadSearch
        simpa [search] using hfuel
      have hHead : Fires (K :: P) K (.atom a) :=
        by simpa [K] using fires_to_derives hHeadBool
      have hφDer : Derives (K :: P) (encode φ) :=
        cps_conj_left_from_head (by simpa [K] using hHead)
      rcases derives_to_search hφDer with ⟨fuelφ, hfuelφ⟩
      exact ⟨fuelφ, search_strengthen_fresh_head
        (haK := by simp [K, goalAtoms, atomVarAtoms])
        (hK_fires_only_a := by
          intro P v hF
          exact cps_conj_K_fires_only_for (φ := φ) (ψ := ψ) (a := a) hF)
        fuelφ P (encode φ) haEncodeφ haP hfuelφ⟩

theorem cps_conj_extract_left_from_fresh_body_of_resolution
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeφ : a ∉ goalAtoms (encode φ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hResolve :
      ∀ {fuel : Nat},
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true ∨
            SearchSupports P (encode φ)) :
    SearchSupports P (encode φ) := by
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have hAtom' : Derives (K :: P) (.atom (.atom a)) :=
    cps_conj_atom_from_sub hSub
  rcases derives_to_search hAtom' with ⟨fuel, hfuel⟩
  cases fuel with
  | zero =>
      simp [search] at hfuel
  | succ fuel =>
      have hResolved := hResolve (by simpa [search] using hfuel)
      rcases hResolved with hHeadBool | hφ
      · have hHead : Fires (K :: P) K (.atom a) :=
          by simpa [K] using fires_to_derives hHeadBool
        have hφDer : Derives (K :: P) (encode φ) :=
          cps_conj_left_from_head (by simpa [K] using hHead)
        rcases derives_to_search hφDer with ⟨fuelφ, hfuelφ⟩
        exact ⟨fuelφ, search_strengthen_fresh_head
          (haK := by simp [K, goalAtoms, atomVarAtoms])
          (hK_fires_only_a := by
            intro P v hF
            exact cps_conj_K_fires_only_for (φ := φ) (ψ := ψ) (a := a) hF)
          fuelφ P (encode φ) haEncodeφ haP hfuelφ⟩
      · exact hφ

/--
Focused classification for `searchAnyAssumption`: a successful boolean search for
an atom exposes a concrete clause in the scanned list that fires to that atom.

This is the first step in replacing the raw weakened-resolution boolean premise
with a focused HH-style classification surface.
-/
private theorem searchAnyAssumption_true_iff_exists_fires
    {fuel : Nat} {P : Program} {gs : List Goal} {v : AtomVar} :
    searchAnyAssumption fuel P gs v = true ↔ ∃ g, g ∈ gs ∧ fires fuel P g v = true := by
  induction gs with
  | nil =>
      simp [searchAnyAssumption]
  | cons g gs ih =>
      simp [searchAnyAssumption, ih, Bool.or_eq_true]

/--
For the conjunction fresh-head search surface, success of
`searchAnyAssumption fuel (K :: P) (K :: P) (.atom a)` means either the head `K`
fires, or some ambient clause in `P` fires to the same atom.

This is the precise focused decomposition suggested by the HH literature:
separate the head-focused branch from the ambient-focused branch before trying to
prove the weaker resolution theorem.
-/
theorem cps_conj_searchAnyAssumption_head_or_ambient
    {P : Program} (φ ψ : IPL) {a : Atom} {fuel : Nat}
    (hAny :
      searchAnyAssumption fuel
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.atom a) = true) :
    fires fuel
      (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
      (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
      (.atom a) = true ∨
      ∃ D, D ∈ P ∧
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          D
          (.atom a) = true := by
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have hSplit :
      fires fuel (K :: P) K (.atom a) = true ∨
        searchAnyAssumption fuel (K :: P) P (.atom a) = true := by
    simpa [K, searchAnyAssumption, Bool.or_eq_true] using hAny
  rcases hSplit with hHead | hTail
  · exact Or.inl (by simpa [K] using hHead)
  · rcases (searchAnyAssumption_true_iff_exists_fires (P := K :: P) (gs := P) (v := .atom a)).mp hTail with
      ⟨D, hDP, hFire⟩
    exact Or.inr ⟨D, hDP, hFire⟩

/--
Boolean-level version of the fresh conjunction head/ambient split for atom
searches in `K :: P`.

Unlike the derivation-level splitter below, this theorem preserves the exact
successful search fuel. That is the surface needed by the residual
implication-root recursive worker.
-/
private theorem cps_conj_search_atom_head_or_ambient
    {P : Program} (φ ψ : IPL) {a : Atom} {fuel : Nat}
    (hSearch :
      search (fuel + 1)
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.atom (.atom a)) = true) :
    fires fuel
      (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
      (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
      (.atom a) = true ∨
      ∃ D, D ∈ P ∧
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          D
          (.atom a) = true := by
  have hAny :
      searchAnyAssumption fuel
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.atom a) = true := by
    simpa [search] using hSearch
  exact
    cps_conj_searchAnyAssumption_head_or_ambient
      (P := P) φ ψ (a := a) (fuel := fuel) hAny

/--
Any atom appearing in a goal that belongs to a program also appears in the
program's atom inventory.
-/
private theorem mem_programAtoms_of_mem_goal_bridge {P : Program} {g : Goal} {a : Atom}
    (hg : g ∈ P) (ha : a ∈ goalAtoms g) :
    a ∈ programAtoms P := by
  induction P with
  | nil =>
      cases hg
  | cons head tail ih =>
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · have : a ∈ goalAtoms g ++ programAtoms tail := List.mem_append.mpr (Or.inl ha)
        simpa [programAtoms] using this
      · have htail : a ∈ programAtoms tail := ih hg
        have : a ∈ goalAtoms head ++ programAtoms tail := List.mem_append.mpr (Or.inr htail)
        simpa [programAtoms] using this

private theorem atomVarAtoms_substAtomVar_avoids_atom_bridge
    {v : AtomVar} {a atm : Atom} {n : Nat}
    (ha : a ∉ atomVarAtoms v) (hatm : atm ≠ a) :
    a ∉ atomVarAtoms (substAtomVar n atm v) := by
  cases v with
  | atom b =>
      simpa [substAtomVar, atomVarAtoms] using ha
  | bvar k =>
      cases n with
      | zero =>
          by_cases hk : k = 0
          · subst hk
            simp [substAtomVar, atomVarAtoms]
            exact fun h => hatm h.symm
          · simp [substAtomVar, atomVarAtoms, hk]
      | succ n =>
          cases k with
          | zero =>
              simp [substAtomVar, atomVarAtoms]
          | succ k =>
              by_cases hk : k = n
              · simp [substAtomVar, atomVarAtoms, hk]
                exact fun h => hatm h.symm
              · simp [substAtomVar, atomVarAtoms, hk]

private theorem goalAtoms_substGoal_avoids_atom_bridge
    {g : Goal} {a atm : Atom} {n : Nat}
    (ha : a ∉ goalAtoms g) (hatm : atm ≠ a) :
    a ∉ goalAtoms (substGoal g n atm) := by
  induction g generalizing n with
  | atom v =>
      simpa [goalAtoms, substGoal] using
        atomVarAtoms_substAtomVar_avoids_atom_bridge (a := a) (atm := atm) (n := n) (v := v)
          (by simpa [goalAtoms] using ha) hatm
  | imp g₁ g₂ ih₁ ih₂ =>
      have ha₁ : a ∉ goalAtoms g₁ := by
        intro hm
        exact ha (by simp [goalAtoms, hm])
      have ha₂ : a ∉ goalAtoms g₂ := by
        intro hm
        exact ha (by simp [goalAtoms, hm])
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ih₁ (n := n) ha₁ hm
      · exact ih₂ (n := n) ha₂ hm
  | conj g₁ g₂ ih₁ ih₂ =>
      have ha₁ : a ∉ goalAtoms g₁ := by
        intro hm
        exact ha (by simp [goalAtoms, hm])
      have ha₂ : a ∉ goalAtoms g₂ := by
        intro hm
        exact ha (by simp [goalAtoms, hm])
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ih₁ (n := n) ha₁ hm
      · exact ih₂ (n := n) ha₂ hm
  | disj g₁ g₂ ih₁ ih₂ =>
      have ha₁ : a ∉ goalAtoms g₁ := by
        intro hm
        exact ha (by simp [goalAtoms, hm])
      have ha₂ : a ∉ goalAtoms g₂ := by
        intro hm
        exact ha (by simp [goalAtoms, hm])
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ih₁ (n := n) ha₁ hm
      · exact ih₂ (n := n) ha₂ hm
  | all g ih =>
      have ha' : a ∉ goalAtoms g := by
        simpa [goalAtoms] using ha
      simpa [substGoal, goalAtoms] using ih (n := n + 1) ha'

/--
If an ambient clause from `P` fires to a fresh atom `a`, its outer constructor
cannot be `atom`, `conj`, or `disj`. The only remaining constructor shapes are
`imp` and `all`.

This is the first real case split for the remaining ambient-clause blocker.
-/
theorem ambient_fires_fresh_atom_constructor
    {P R : Program} {D : Goal} {a : Atom} {fuel : Nat}
    (hDP : D ∈ P)
    (haP : a ∉ programAtoms P)
    (hFire : fires fuel R D (.atom a) = true) :
    (∃ g₁ g₂, D = .imp g₁ g₂) ∨ ∃ g, D = .all g := by
  cases D with
  | atom v =>
      cases fuel with
      | zero =>
          simp [fires] at hFire
      | succ fuel =>
          cases v with
          | atom b =>
              have hab : b = a := by
                simpa [fires] using hFire
              apply False.elim
              apply haP
              exact mem_programAtoms_of_mem_goal_bridge hDP (by
                subst hab
                simp [goalAtoms, atomVarAtoms])
          | bvar k =>
              simp [fires] at hFire
  | imp g₁ g₂ =>
      exact Or.inl ⟨g₁, g₂, rfl⟩
  | conj g₁ g₂ =>
      cases fuel with
      | zero =>
          simp [fires] at hFire
      | succ fuel =>
          simp [fires] at hFire
  | disj g₁ g₂ =>
      cases fuel with
      | zero =>
          simp [fires] at hFire
      | succ fuel =>
          simp [fires] at hFire
  | all g =>
      exact Or.inr ⟨g, rfl⟩

/--
Any ambient fire to the fresh continuation atom reduces to a same-atom universal
body fire.

This collapses all fresh ambient implication tails to the single genuinely hard
obstruction: a universally quantified body instantiated at the target atom and
still firing that same atom.
-/
private theorem cps_conj_ambient_fire_reduces_to_all_body
    {P : Program} (φ ψ : IPL) {g : Goal} {a : Atom}
    (haG : a ∉ goalAtoms g)
    (haP : a ∉ programAtoms P)
    (hFire :
      Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P) g (.atom a)) :
    ∃ body, a ∉ goalAtoms body ∧
      Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (substGoal body 0 a) (.atom a) := by
  induction g generalizing a with
  | atom v =>
      cases v with
      | atom b =>
          cases hFire
          exfalso
          exact haG (by simp [goalAtoms, atomVarAtoms])
      | bvar k =>
          cases hFire
  | imp g₁ g₂ ih₁ ih₂ =>
      cases hFire with
      | imp hPrem hTail =>
          have haTail : a ∉ goalAtoms g₂ := by
            intro hm
            exact haG (by simp [goalAtoms, hm])
          exact ih₂ haTail haP hTail
  | conj g₁ g₂ ih₁ ih₂ =>
      cases hFire
  | disj g₁ g₂ ih₁ ih₂ =>
      cases hFire
  | all body ih =>
      cases hFire
      rename_i hsub
      exact ⟨body, by simpa [goalAtoms] using haG, hsub⟩

theorem cps_conj_extract_left_from_fresh_body_of_ambient_clause
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeφ : a ∉ goalAtoms (encode φ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hAmbient :
      ∀ {D : Goal} {fuel : Nat},
        D ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          D
          (.atom a) = true →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode φ) := by
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have hAtom' : Derives (K :: P) (.atom (.atom a)) :=
    cps_conj_atom_from_sub hSub
  rcases derives_to_search hAtom' with ⟨fuel, hfuel⟩
  cases fuel with
  | zero =>
      simp [search] at hfuel
  | succ fuel =>
      have hSplit :=
        cps_conj_searchAnyAssumption_head_or_ambient (P := P) φ ψ (a := a)
          (fuel := fuel) (by simpa [search] using hfuel)
      rcases hSplit with hHeadBool | ⟨D, hDP, hFireD⟩
      · have hHead : Fires (K :: P) K (.atom a) :=
          by simpa [K] using fires_to_derives hHeadBool
        have hφDer : Derives (K :: P) (encode φ) :=
          cps_conj_left_from_head (by simpa [K] using hHead)
        rcases derives_to_search hφDer with ⟨fuelφ, hfuelφ⟩
        exact ⟨fuelφ, search_strengthen_fresh_head
          (haK := by simp [K, goalAtoms, atomVarAtoms])
          (hK_fires_only_a := by
            intro P v hF
            exact cps_conj_K_fires_only_for (φ := φ) (ψ := ψ) (a := a) hF)
          fuelφ P (encode φ) haEncodeφ haP hfuelφ⟩
      · exact hAmbient hDP hFireD

theorem cps_conj_extract_left_from_fresh_body_of_ambient_constructor_cases
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeφ : a ∉ goalAtoms (encode φ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hAmbientImp :
      ∀ {g₁ g₂ : Goal} {fuel : Nat},
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAll :
      ∀ {g : Goal} {fuel : Nat},
        Goal.all g ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all g)
          (.atom a) = true →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode φ) := by
  exact cps_conj_extract_left_from_fresh_body_of_ambient_clause φ ψ haEncodeφ haP hSub
    (fun {D} {fuel} hDP hFireD =>
      match ambient_fires_fresh_atom_constructor (P := P) (R := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        hDP haP hFireD with
      | Or.inl ⟨g₁, g₂, hD⟩ => by
          subst hD
          exact hAmbientImp hDP hFireD
      | Or.inr ⟨g, hD⟩ => by
          subst hD
          exact hAmbientAll hDP hFireD)

theorem cps_conj_extract_left_from_fresh_body_of_ambient_all_member_cases
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeφ : a ∉ goalAtoms (encode φ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hAmbientImp :
      ∀ {g₁ g₂ : Goal} {fuel : Nat},
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImp :
      ∀ {g₁ g₂ : Goal} {fuel : Nat},
        Goal.all (.imp g₁ g₂) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ g₂))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllAll :
      ∀ {g : Goal} {fuel : Nat},
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode φ) := by
  exact cps_conj_extract_left_from_fresh_body_of_ambient_constructor_cases φ ψ haEncodeφ haP hSub
    hAmbientImp
    (by
      intro g fuel hDP hFireD
      cases g with
      | atom v =>
          cases v with
          | atom b =>
              have hFire : Fires
                  (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                  (.all (.atom (.atom b)))
                  (.atom a) := by
                simpa using fires_to_derives hFireD
              have hRed :
                  Fires
                    (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                    (.atom (.atom b))
                    (.atom a) :=
                fires_all_atom_reduce hFire
              have hab : b = a := by
                cases hRed
                rfl
              exfalso
              exact haP <|
                mem_programAtoms_of_mem_goal_bridge hDP (by
                  subst hab
                  simp [goalAtoms, atomVarAtoms])
          | bvar k =>
              cases k with
              | zero =>
                  exact search_encode_of_all_top_member hDP φ
              | succ k =>
                  have hFire :
                      Fires
                        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                        (.all (.atom (.bvar (Nat.succ k))))
                        (.atom a) := by
                    simpa using fires_to_derives hFireD
                  exact False.elim <|
                    fires_subst_atom_succ_bvar_atom_false
                      (P := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                      (k := k) (atm := a)
                      (fires_all_atom_reduce hFire)
      | imp g₁ g₂ =>
          exact hAmbientAllImp hDP hFireD
      | conj g₁ g₂ =>
          have hFire :
              Fires
                (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                (.all (.conj g₁ g₂))
                (.atom a) := by
            simpa using fires_to_derives hFireD
          exact False.elim <|
            fires_subst_conj_atom_false
              (P := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
              (g₁ := g₁) (g₂ := g₂) (atm := a)
              (fires_all_atom_reduce hFire)
      | disj g₁ g₂ =>
          have hFire :
              Fires
                (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                (.all (.disj g₁ g₂))
                (.atom a) := by
            simpa using fires_to_derives hFireD
          exact False.elim <|
            fires_subst_disj_atom_false
              (P := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
              (g₁ := g₁) (g₂ := g₂) (atm := a)
              (fires_all_atom_reduce hFire)
      | all g =>
          exact hAmbientAllAll hDP hFireD)

theorem cps_conj_extract_left_from_fresh_body_of_all_body_obstruction
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeφ : a ∉ goalAtoms (encode φ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hAllBody :
      ∀ {body : Goal},
        a ∉ goalAtoms body →
        Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (substGoal body 0 a)
          (.atom a) →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode φ) := by
  exact cps_conj_extract_left_from_fresh_body_of_ambient_constructor_cases φ ψ haEncodeφ haP hSub
    (by
      intro g₁ g₂ fuel hDP hFireD
      have hFire : Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂) (.atom a) := by
        simpa using fires_to_derives hFireD
      have haImp : a ∉ goalAtoms (.imp g₁ g₂) := by
        intro hm
        exact haP (mem_programAtoms_of_mem_goal_bridge hDP hm)
      rcases cps_conj_ambient_fire_reduces_to_all_body (P := P) φ ψ haImp haP hFire with
        ⟨body, haBody, hBodyFire⟩
      exact hAllBody haBody hBodyFire)
    (by
      intro body fuel hDP hFireD
      have hFire : Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all body) (.atom a) := by
        simpa using fires_to_derives hFireD
      have haBody : a ∉ goalAtoms body := by
        intro hm
        exact haP (mem_programAtoms_of_mem_goal_bridge hDP (by simp [goalAtoms, hm]))
      exact hAllBody haBody (fires_all_atom_reduce hFire))

theorem cps_conj_extract_right_from_fresh_body
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeψ : a ∉ goalAtoms (encode ψ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hHeadSearch :
      ∀ {fuel : Nat},
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true) :
    SearchSupports P (encode ψ) := by
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have hAtom' : Derives (K :: P) (.atom (.atom a)) :=
    cps_conj_atom_from_sub hSub
  rcases derives_to_search hAtom' with ⟨fuel, hfuel⟩
  cases fuel with
  | zero =>
      simp [search] at hfuel
  | succ fuel =>
      have hHeadBool : fires fuel (K :: P) K (.atom a) = true := by
        apply hHeadSearch
        simpa [search] using hfuel
      have hHead : Fires (K :: P) K (.atom a) :=
        by simpa [K] using fires_to_derives hHeadBool
      have hψDer : Derives (K :: P) (encode ψ) :=
        cps_conj_right_from_head (by simpa [K] using hHead)
      rcases derives_to_search hψDer with ⟨fuelψ, hfuelψ⟩
      exact ⟨fuelψ, search_strengthen_fresh_head
        (haK := by simp [K, goalAtoms, atomVarAtoms])
        (hK_fires_only_a := by
          intro P v hF
          exact cps_conj_K_fires_only_for (φ := φ) (ψ := ψ) (a := a) hF)
        fuelψ P (encode ψ) haEncodeψ haP hfuelψ⟩

theorem cps_conj_extract_right_from_fresh_body_of_resolution
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeψ : a ∉ goalAtoms (encode ψ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hResolve :
      ∀ {fuel : Nat},
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true ∨
            SearchSupports P (encode ψ)) :
    SearchSupports P (encode ψ) := by
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have hAtom' : Derives (K :: P) (.atom (.atom a)) :=
    cps_conj_atom_from_sub hSub
  rcases derives_to_search hAtom' with ⟨fuel, hfuel⟩
  cases fuel with
  | zero =>
      simp [search] at hfuel
  | succ fuel =>
      have hResolved := hResolve (by simpa [search] using hfuel)
      rcases hResolved with hHeadBool | hψ
      · have hHead : Fires (K :: P) K (.atom a) :=
          by simpa [K] using fires_to_derives hHeadBool
        have hψDer : Derives (K :: P) (encode ψ) :=
          cps_conj_right_from_head (by simpa [K] using hHead)
        rcases derives_to_search hψDer with ⟨fuelψ, hfuelψ⟩
        exact ⟨fuelψ, search_strengthen_fresh_head
          (haK := by simp [K, goalAtoms, atomVarAtoms])
          (hK_fires_only_a := by
            intro P v hF
            exact cps_conj_K_fires_only_for (φ := φ) (ψ := ψ) (a := a) hF)
          fuelψ P (encode ψ) haEncodeψ haP hfuelψ⟩
      · exact hψ

theorem cps_conj_extract_right_from_fresh_body_of_ambient_clause
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeψ : a ∉ goalAtoms (encode ψ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hAmbient :
      ∀ {D : Goal} {fuel : Nat},
        D ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          D
          (.atom a) = true →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode ψ) := by
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have hAtom' : Derives (K :: P) (.atom (.atom a)) :=
    cps_conj_atom_from_sub hSub
  rcases derives_to_search hAtom' with ⟨fuel, hfuel⟩
  cases fuel with
  | zero =>
      simp [search] at hfuel
  | succ fuel =>
      have hSplit :=
        cps_conj_searchAnyAssumption_head_or_ambient (P := P) φ ψ (a := a)
          (fuel := fuel) (by simpa [search] using hfuel)
      rcases hSplit with hHeadBool | ⟨D, hDP, hFireD⟩
      · have hHead : Fires (K :: P) K (.atom a) :=
          by simpa [K] using fires_to_derives hHeadBool
        have hψDer : Derives (K :: P) (encode ψ) :=
          cps_conj_right_from_head (by simpa [K] using hHead)
        rcases derives_to_search hψDer with ⟨fuelψ, hfuelψ⟩
        exact ⟨fuelψ, search_strengthen_fresh_head
          (haK := by simp [K, goalAtoms, atomVarAtoms])
          (hK_fires_only_a := by
            intro P v hF
            exact cps_conj_K_fires_only_for (φ := φ) (ψ := ψ) (a := a) hF)
          fuelψ P (encode ψ) haEncodeψ haP hfuelψ⟩
      · exact hAmbient hDP hFireD

theorem cps_conj_extract_right_from_fresh_body_of_ambient_constructor_cases
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeψ : a ∉ goalAtoms (encode ψ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hAmbientImp :
      ∀ {g₁ g₂ : Goal} {fuel : Nat},
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAll :
      ∀ {g : Goal} {fuel : Nat},
        Goal.all g ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all g)
          (.atom a) = true →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode ψ) := by
  exact cps_conj_extract_right_from_fresh_body_of_ambient_clause φ ψ haEncodeψ haP hSub
    (fun {D} {fuel} hDP hFireD =>
      match ambient_fires_fresh_atom_constructor (P := P) (R := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        hDP haP hFireD with
      | Or.inl ⟨g₁, g₂, hD⟩ => by
          subst hD
          exact hAmbientImp hDP hFireD
      | Or.inr ⟨g, hD⟩ => by
          subst hD
          exact hAmbientAll hDP hFireD)

theorem cps_conj_extract_right_from_fresh_body_of_ambient_all_member_cases
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeψ : a ∉ goalAtoms (encode ψ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hAmbientImp :
      ∀ {g₁ g₂ : Goal} {fuel : Nat},
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImp :
      ∀ {g₁ g₂ : Goal} {fuel : Nat},
        Goal.all (.imp g₁ g₂) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ g₂))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllAll :
      ∀ {g : Goal} {fuel : Nat},
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode ψ) := by
  exact cps_conj_extract_right_from_fresh_body_of_ambient_constructor_cases φ ψ haEncodeψ haP hSub
    hAmbientImp
    (by
      intro g fuel hDP hFireD
      cases g with
      | atom v =>
          cases v with
          | atom b =>
              have hFire : Fires
                  (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                  (.all (.atom (.atom b)))
                  (.atom a) := by
                simpa using fires_to_derives hFireD
              have hRed :
                  Fires
                    (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                    (.atom (.atom b))
                    (.atom a) :=
                fires_all_atom_reduce hFire
              have hab : b = a := by
                cases hRed
                rfl
              exfalso
              exact haP <|
                mem_programAtoms_of_mem_goal_bridge hDP (by
                  subst hab
                  simp [goalAtoms, atomVarAtoms])
          | bvar k =>
              cases k with
              | zero =>
                  exact search_encode_of_all_top_member hDP ψ
              | succ k =>
                  have hFire :
                      Fires
                        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                        (.all (.atom (.bvar (Nat.succ k))))
                        (.atom a) := by
                    simpa using fires_to_derives hFireD
                  exact False.elim <|
                    fires_subst_atom_succ_bvar_atom_false
                      (P := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                      (k := k) (atm := a)
                      (fires_all_atom_reduce hFire)
      | imp g₁ g₂ =>
          exact hAmbientAllImp hDP hFireD
      | conj g₁ g₂ =>
          have hFire :
              Fires
                (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                (.all (.conj g₁ g₂))
                (.atom a) := by
            simpa using fires_to_derives hFireD
          exact False.elim <|
            fires_subst_conj_atom_false
              (P := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
              (g₁ := g₁) (g₂ := g₂) (atm := a)
              (fires_all_atom_reduce hFire)
      | disj g₁ g₂ =>
          have hFire :
              Fires
                (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
                (.all (.disj g₁ g₂))
                (.atom a) := by
            simpa using fires_to_derives hFireD
          exact False.elim <|
            fires_subst_disj_atom_false
              (P := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
              (g₁ := g₁) (g₂ := g₂) (atm := a)
              (fires_all_atom_reduce hFire)
      | all g =>
          exact hAmbientAllAll hDP hFireD)

/--
If an ambient member `∀X.(g₁ -> g₂)` fires the fresh continuation atom, then the
tail `g₂` can only be one of the live recursive shapes:

- `atom (bvar 0)` (the top-tail branch)
- `imp u v`
- `all u`

All other tail roots are incompatible with firing the fresh continuation atom.
-/
private theorem cps_conj_ambient_all_imp_tail_fresh_atom_cases
    {P : Program} (φ ψ : IPL) {g₁ g₂ : Goal} {a : Atom} {fuel : Nat}
    (hDP : Goal.all (.imp g₁ g₂) ∈ P)
    (haP : a ∉ programAtoms P)
    (hFireD :
      fires fuel
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.all (.imp g₁ g₂))
        (.atom a) = true) :
    g₂ = .atom (.bvar 0) ∨ (∃ u v, g₂ = .imp u v) ∨ ∃ u, g₂ = .all u := by
  have hFire :
      Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.all (.imp g₁ g₂))
        (.atom a) := by
    simpa using fires_to_derives hFireD
  have hRed :
      Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (substGoal g₂ 0 a)
        (.atom a) := by
    have hAllRed :
        Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (substGoal (.imp g₁ g₂) 0 a)
          (.atom a) :=
      fires_all_atom_reduce hFire
    simpa [substGoal] using
      (match hAllRed with
      | .imp _ hTail => hTail)
  have haG₂ : a ∉ goalAtoms g₂ := by
    intro hm
    exact haP <|
      mem_programAtoms_of_mem_goal_bridge hDP (by simp [goalAtoms, hm])
  cases g₂ with
  | atom v =>
      cases v with
      | atom b =>
          cases hRed
          exfalso
          exact haG₂ (by simp [goalAtoms, atomVarAtoms])
      | bvar k =>
          cases k with
          | zero =>
              exact Or.inl rfl
          | succ k =>
              cases hRed
  | imp u v =>
      exact Or.inr <| Or.inl ⟨u, v, rfl⟩
  | conj u v =>
      cases hRed
  | disj u v =>
      cases hRed
  | all u =>
      exact Or.inr <| Or.inr ⟨u, rfl⟩

/--
Boolean-to-derivation inversion for the recursive ambient implication-member
branch in the conjunction head context.

When `∀X.(g₁ -> g₂)` fires the target atom `a`, the instantiated premise and
tail are exposed directly as derivation data in `K :: P`.
-/
private theorem cps_conj_ambient_all_imp_fire_cases
    {P : Program} (φ ψ : IPL) {g₁ g₂ : Goal} {a : Atom} {fuel : Nat}
    (hFireD :
      fires fuel
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.all (.imp g₁ g₂))
        (.atom a) = true) :
    Derives (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
      (substGoal g₁ 0 a) ∧
      Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (substGoal g₂ 0 a)
        (.atom a) := by
  have hFire :
      Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.all (.imp g₁ g₂))
        (.atom a) := by
    simpa using fires_to_derives hFireD
  have hRed :
      Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.imp (substGoal g₁ 0 a) (substGoal g₂ 0 a))
        (.atom a) := by
    simpa [substGoal] using fires_all_atom_reduce hFire
  exact
    match hRed with
    | .imp hPrem hTail => ⟨hPrem, hTail⟩

/--
Boolean-to-derivation inversion for the recursive ambient universal-member
branch in the conjunction head context.

Firing `∀X.∀Y.g` to the target atom `a` reduces to the doubly-instantiated body
that still fires `a` in `K :: P`.
-/
private theorem cps_conj_ambient_all_all_fire_case
    {P : Program} (φ ψ : IPL) {g : Goal} {a : Atom} {fuel : Nat}
    (hFireD :
      fires fuel
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.all (.all g))
        (.atom a) = true) :
    Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
      (substGoal (substGoal g 1 a) 0 a)
      (.atom a) := by
  have hFire :
      Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.all (.all g))
        (.atom a) := by
    simpa using fires_to_derives hFireD
  have hRed :
      Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (substGoal (.all g) 0 a)
        (.atom a) := by
    exact fires_all_atom_reduce hFire
  simpa [substGoal] using fires_all_atom_reduce hRed

/--
Exact smaller-fuel split for the residual top-`conj` callback.

If `∀X.((u ∧ v) -> X)` fires the target atom `a` from `K :: P`, the proof
obligation immediately reduces to successful searches for both instantiated
conjuncts at the predecessor fuel.
-/
private theorem cps_conj_ambient_all_imp_top_conj_search_cases
    {P : Program} (φ ψ : IPL) {u v : Goal} {a : Atom} {fuel : Nat}
    (hFireD :
      fires (fuel + 3)
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.all (.imp (.conj u v) (.atom (.bvar 0))))
        (.atom a) = true) :
    search fuel
      (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
      (substGoal u 0 a) = true ∧
      search fuel
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (substGoal v 0 a) = true := by
  have h3 : fuel + 3 = (fuel + 2).succ := by omega
  have h2 : fuel + 2 = (fuel + 1).succ := by omega
  have h1 : fuel + 1 = fuel.succ := by omega
  rw [h3, fires.eq_6] at hFireD
  simp only [substGoal] at hFireD
  rw [h2, fires.eq_3, Bool.and_eq_true] at hFireD
  rcases hFireD with ⟨hSearchConj, _hAtom⟩
  rw [h1, search.eq_4, Bool.and_eq_true] at hSearchConj
  simpa [substGoal] using hSearchConj

/--
Derivation-side inversion for the top-`conj` implication-root branch.

When `∀X.((u ∧ v) -> X)` fires the target atom `a`, the instantiated premise
derivation in `K :: P` immediately splits into derivations of both instantiated
conjuncts.
-/
private theorem cps_conj_ambient_all_imp_top_conj_derived_conjuncts
    {P : Program} (φ ψ : IPL) {u v : Goal} {a : Atom} {fuel : Nat}
    (hFireD :
      fires fuel
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.all (.imp (.conj u v) (.atom (.bvar 0))))
        (.atom a) = true) :
    Derives (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
      (substGoal u 0 a) ∧
      Derives (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (substGoal v 0 a) := by
  have hPrem :
      Derives (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (substGoal (.conj u v) 0 a) :=
    (cps_conj_ambient_all_imp_fire_cases
      (P := P) φ ψ
      (g₁ := .conj u v)
      (g₂ := .atom (.bvar 0))
      (a := a)
      (fuel := fuel)
      hFireD).1
  simpa [substGoal] using derives_conj_inversion hPrem

/--
Focused structural classification for a fixed top-tail ambient implication
member in the conjunction head context.

This preserves the exact ambient member provenance while exposing the extra
derivation data available only in the `prem = conj _ _` branch.
-/
private theorem cps_conj_ambient_all_imp_top_member_focused_cases
    {P : Program} (φ ψ : IPL) {prem : Goal} {a : Atom} {fuel : Nat}
    (hDP : Goal.all (.imp prem (.atom (.bvar 0))) ∈ P)
    (_haP : a ∉ programAtoms P)
    (hFireD :
      fires fuel
        (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
        (.all (.imp prem (.atom (.bvar 0))))
        (.atom a) = true) :
    (∃ v, prem = .atom v) ∨
      (∃ u v,
        prem = .conj u v ∧
        Derives (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (substGoal u 0 a) ∧
        Derives (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (substGoal v 0 a)) ∨
      (∃ u v, prem = .imp u v) ∨
      (∃ u v, prem = .disj u v) ∨
      ∃ u, prem = .all u := by
  cases prem with
  | atom v =>
      exact Or.inl ⟨v, rfl⟩
  | imp u v =>
      exact Or.inr <| Or.inr <| Or.inl ⟨u, v, rfl⟩
  | conj u v =>
      rcases cps_conj_ambient_all_imp_top_conj_derived_conjuncts
          (P := P) φ ψ (u := u) (v := v) (a := a) (fuel := fuel) hFireD with
        ⟨hDu, hDv⟩
      exact Or.inr <| Or.inl ⟨u, v, rfl, hDu, hDv⟩
  | disj u v =>
      exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨u, v, rfl⟩
  | all u =>
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨u, rfl⟩

theorem cps_conj_extract_right_from_fresh_body_of_all_body_obstruction
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeψ : a ∉ goalAtoms (encode ψ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hAllBody :
      ∀ {body : Goal},
        a ∉ goalAtoms body →
        Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (substGoal body 0 a)
          (.atom a) →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode ψ) := by
  exact cps_conj_extract_right_from_fresh_body_of_ambient_constructor_cases φ ψ haEncodeψ haP hSub
    (by
      intro g₁ g₂ fuel hDP hFireD
      have hFire : Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂) (.atom a) := by
        simpa using fires_to_derives hFireD
      have haImp : a ∉ goalAtoms (.imp g₁ g₂) := by
        intro hm
        exact haP (mem_programAtoms_of_mem_goal_bridge hDP hm)
      rcases cps_conj_ambient_fire_reduces_to_all_body (P := P) φ ψ haImp haP hFire with
        ⟨body, haBody, hBodyFire⟩
      exact hAllBody haBody hBodyFire)
    (by
      intro body fuel hDP hFireD
      have hFire : Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all body) (.atom a) := by
        simpa using fires_to_derives hFireD
      have haBody : a ∉ goalAtoms body := by
        intro hm
        exact haP (mem_programAtoms_of_mem_goal_bridge hDP (by simp [goalAtoms, hm]))
      exact hAllBody haBody (fires_all_atom_reduce hFire))

/--
Program-level conjunction extraction, assuming the exact missing head-search
premise for fresh continuation atoms.

This packages the arbitrary-program part of the old atomic-base proof cleanly:
the extractor itself is now independent of the atomic-base representation. The
only remaining debt is to justify `hHeadSearch` on the desired program class.
-/
theorem cps_conj_extract_left_of_head_search
    {P : Program} (φ ψ : IPL)
    (hHeadSearch :
      ∀ {a : Atom} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode φ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeφ : a ∉ goalAtoms (encode φ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_left_from_fresh_body_of_resolution φ ψ haEncodeφ haP hSub'
    (fun {fuel} hAny => Or.inl (hHeadSearch haEncodeφ haP hAny))

theorem cps_conj_extract_left_of_resolution
    {P : Program} (φ ψ : IPL)
    (hResolve :
      ∀ {a : Atom} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true ∨
            SearchSupports P (encode φ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode φ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeφ : a ∉ goalAtoms (encode φ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_left_from_fresh_body_of_resolution φ ψ haEncodeφ haP hSub'
    (fun {fuel} hAny => hResolve haEncodeφ haP hAny)

theorem cps_conj_extract_left_of_ambient_clause
    {P : Program} (φ ψ : IPL)
    (hAmbient :
      ∀ {a : Atom} {D : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        D ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          D
          (.atom a) = true →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode φ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeφ : a ∉ goalAtoms (encode φ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_left_from_fresh_body_of_ambient_clause φ ψ haEncodeφ haP hSub'
    (fun {D} {fuel} hDP hFireD => hAmbient haEncodeφ haP hDP hFireD)

theorem cps_conj_extract_left_of_ambient_constructor_cases
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all g ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all g)
          (.atom a) = true →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode φ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeφ : a ∉ goalAtoms (encode φ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_left_from_fresh_body_of_ambient_constructor_cases φ ψ haEncodeφ haP hSub'
    (fun {g₁} {g₂} {fuel} hDP hFireD => hAmbientImp haEncodeφ haP hDP hFireD)
    (fun {g} {fuel} hDP hFireD => hAmbientAll haEncodeφ haP hDP hFireD)

theorem cps_conj_extract_left_of_ambient_all_member_cases
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ g₂) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ g₂))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode φ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeφ : a ∉ goalAtoms (encode φ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' : Derives P (.imp K (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_left_from_fresh_body_of_ambient_all_member_cases φ ψ haEncodeφ haP hSub'
    (fun {g₁} {g₂} {fuel} hDP hFireD => hAmbientImp haEncodeφ haP hDP hFireD)
    (fun {g₁} {g₂} {fuel} hDP hFireD => hAmbientAllImp haEncodeφ haP hDP hFireD)
    (fun {g} {fuel} hDP hFireD => hAmbientAllAll haEncodeφ haP hDP hFireD)

theorem cps_conj_extract_left_of_ambient_all_imp_tail_cases
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpTop :
      ∀ {a : Atom} {g₁ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode φ) := by
  intro h
  exact cps_conj_extract_left_of_ambient_all_member_cases (P := P) φ ψ
    hAmbientImp
    (fun {a} {g₁} {g₂} {fuel} haEncodeφ haP hDP hFireD =>
      by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          exact hAmbientAllImpTop haEncodeφ haP hDP hFireD
        · rcases hImp with ⟨u, v, rfl⟩
          exact hAmbientAllImpImp haEncodeφ haP hDP hFireD
        · rcases hAll with ⟨u, rfl⟩
          exact hAmbientAllImpAll haEncodeφ haP hDP hFireD)
    hAmbientAllAll
    h

theorem cps_conj_extract_left_of_ambient_all_imp_root_cases
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpTopAtom :
      ∀ {a : Atom} {v : AtomVar} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.atom v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.atom v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpTopImp :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.imp u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.imp u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpTopDisj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.disj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.disj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpTopConj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.conj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.conj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpTopAll :
      ∀ {a : Atom} {u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.all u) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.all u) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode φ) := by
  intro h
  exact cps_conj_extract_left_of_ambient_all_member_cases (P := P) φ ψ
    hAmbientImp
    (fun {a} {g₁} {g₂} {fuel} haEncodeφ haP hDP hFireD =>
      by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          rcases cps_conj_ambient_all_imp_top_member_focused_cases
              (P := P) φ ψ (prem := g₁) (a := a) (fuel := fuel)
              hDP haP hFireD with
            hAtom | hConj | hImpRoot | hDisj | hAllRoot
          · rcases hAtom with ⟨v, rfl⟩
            exact hAmbientAllImpTopAtom haEncodeφ haP hDP hFireD
          · rcases hConj with ⟨u, v, rfl, _hDu, _hDv⟩
            exact hAmbientAllImpTopConj haEncodeφ haP hDP hFireD
          · rcases hImpRoot with ⟨u, v, rfl⟩
            exact hAmbientAllImpTopImp haEncodeφ haP hDP hFireD
          · rcases hDisj with ⟨u, v, rfl⟩
            exact hAmbientAllImpTopDisj haEncodeφ haP hDP hFireD
          · rcases hAllRoot with ⟨u, rfl⟩
            exact hAmbientAllImpTopAll haEncodeφ haP hDP hFireD
        · rcases hImp with ⟨u, v, rfl⟩
          exact hAmbientAllImpImp haEncodeφ haP hDP hFireD
        · rcases hAll with ⟨u, rfl⟩
          exact hAmbientAllImpAll haEncodeφ haP hDP hFireD)
    hAmbientAllAll
    h

/--
Left conjunction extraction with the residual top-`conj` callback lifted into
the goal-level semantic surface.

Only the `prem = conj _ _` branch is changed: the callback now consumes the two
instantiated conjunct supports in the head context `K :: P` and returns an
ambient `GoalSupports` conclusion.
-/
theorem cps_conj_extract_left_of_ambient_all_imp_root_cases_goal_top_conj
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpTopAtom :
      ∀ {a : Atom} {v : AtomVar} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.atom v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.atom v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpTopImp :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.imp u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.imp u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpTopDisj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.disj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.disj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpTopConj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.conj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.conj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal u 0 a) →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal v 0 a) →
        GoalSupports P (encode φ))
    (hAmbientAllImpTopAll :
      ∀ {a : Atom} {u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.all u) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.all u) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode φ) := by
  intro h
  exact cps_conj_extract_left_of_ambient_all_member_cases (P := P) φ ψ
    hAmbientImp
    (fun {a} {g₁} {g₂} {fuel} haEncodeφ haP hDP hFireD =>
      by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          rcases cps_conj_ambient_all_imp_top_member_focused_cases
              (P := P) φ ψ (prem := g₁) (a := a) (fuel := fuel)
              hDP haP hFireD with
            hAtom | hConj | hImpRoot | hDisj | hAllRoot
          · rcases hAtom with ⟨v, rfl⟩
            exact hAmbientAllImpTopAtom haEncodeφ haP hDP hFireD
          · rcases hConj with ⟨u, v, rfl, hDu, hDv⟩
            have hTopU :
                HeadGoalSupportsCtx
                  [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                  P
                  (substGoal u 0 a) :=
              derives_to_headGoalSupportsCtx_singleton hDu
            have hTopV :
                HeadGoalSupportsCtx
                  [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                  P
                  (substGoal v 0 a) :=
              derives_to_headGoalSupportsCtx_singleton hDv
            have hGoal :
                GoalSupports P (encode φ) :=
              hAmbientAllImpTopConj haEncodeφ haP hDP hFireD hTopU hTopV
            rw [goalSupports_iff_search] at hGoal
            exact hGoal
          · rcases hImpRoot with ⟨u, v, rfl⟩
            exact hAmbientAllImpTopImp haEncodeφ haP hDP hFireD
          · rcases hDisj with ⟨u, v, rfl⟩
            exact hAmbientAllImpTopDisj haEncodeφ haP hDP hFireD
          · rcases hAllRoot with ⟨u, rfl⟩
            exact hAmbientAllImpTopAll haEncodeφ haP hDP hFireD
        · rcases hImp with ⟨u, v, rfl⟩
          exact hAmbientAllImpImp haEncodeφ haP hDP hFireD
        · rcases hAll with ⟨u, rfl⟩
          exact hAmbientAllImpAll haEncodeφ haP hDP hFireD)
    hAmbientAllAll
    h

/--
Left conjunction extraction with the entire top-tail `∀X.(prem -> X)` family
lifted into the goal-level semantic surface.

Whenever the ambient member has tail `atom (bvar 0)`, the Bridge layer derives
the instantiated premise in `K :: P`, packages it as `HeadGoalSupportsCtx [K] P`,
and hands it to a single semantic callback.
-/
theorem cps_conj_extract_left_of_ambient_all_imp_root_cases_goal_top
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpTop :
      ∀ {a : Atom} {prem : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp prem (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp prem (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal prem 0 a) →
        GoalSupports P (encode φ))
    (hAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports P (encode φ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode φ) := by
  intro h
  exact cps_conj_extract_left_of_ambient_all_member_cases (P := P) φ ψ
    hAmbientImp
    (fun {a} {g₁} {g₂} {fuel} haEncodeφ haP hDP hFireD =>
      by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          have hPrem :
              HeadGoalSupportsCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal g₁ 0 a) :=
            derives_to_headGoalSupportsCtx_singleton <|
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .atom (.bvar 0))
                (a := a) (fuel := fuel) hFireD).1
          have hGoal : GoalSupports P (encode φ) :=
            hAmbientAllImpTop haEncodeφ haP hDP hFireD hPrem
          rw [goalSupports_iff_search] at hGoal
          exact hGoal
        · rcases hImp with ⟨u, v, rfl⟩
          exact hAmbientAllImpImp haEncodeφ haP hDP hFireD
        · rcases hAll with ⟨u, rfl⟩
          exact hAmbientAllImpAll haEncodeφ haP hDP hFireD)
    hAmbientAllAll
    h

/--
Left conjunction extraction with the surviving recursive ambient tail callbacks
lifted into the mixed goal-support / goal-fire semantic surface.

This extends `...goal_top`: the top-tail family already speaks through
`HeadGoalSupportsCtx`; the recursive `imp`/`all` tails and the doubly-universal
body now consume the precise head-context firing data exposed by the Bridge
layer.
-/
theorem cps_conj_extract_left_of_ambient_all_imp_root_cases_goal_fire
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          g₁ →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          g₂
          (.atom a) →
        GoalSupports P (encode φ))
    (hAmbientAllImpTop :
      ∀ {a : Atom} {prem : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp prem (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp prem (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal prem 0 a) →
        GoalSupports P (encode φ))
    (hAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal g₁ 0 a) →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal (.imp u v) 0 a)
          (.atom a) →
        GoalSupports P (encode φ))
    (hAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal g₁ 0 a) →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal (.all u) 0 a)
          (.atom a) →
        GoalSupports P (encode φ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal (substGoal g 1 a) 0 a)
          (.atom a) →
        GoalSupports P (encode φ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode φ) := by
  intro h
  exact cps_conj_extract_left_of_ambient_all_member_cases (P := P) φ ψ
    (fun {a} {g₁} {g₂} {fuel} haEncodeφ haP hDP hFireD =>
      by
        rcases fires_imp_to_headGoalSupportsCtx_and_headGoalFires
            (P := P)
            (K := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hFireD with
          ⟨hPrem, hTail⟩
        have hGoal : GoalSupports P (encode φ) :=
          hAmbientImp haEncodeφ haP hDP hFireD hPrem hTail
        rw [goalSupports_iff_search] at hGoal
        exact hGoal)
    (fun {a} {g₁} {g₂} {fuel} haEncodeφ haP hDP hFireD =>
      by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          have hPrem :
              HeadGoalSupportsCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal g₁ 0 a) :=
            derives_to_headGoalSupportsCtx_singleton <|
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .atom (.bvar 0))
                (a := a) (fuel := fuel) hFireD).1
          have hGoal : GoalSupports P (encode φ) :=
            hAmbientAllImpTop haEncodeφ haP hDP hFireD hPrem
          rw [goalSupports_iff_search] at hGoal
          exact hGoal
        · rcases hImp with ⟨u, v, rfl⟩
          have hPrem :
              HeadGoalSupportsCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal g₁ 0 a) :=
            derives_to_headGoalSupportsCtx_singleton <|
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .imp u v)
                (a := a) (fuel := fuel) hFireD).1
          have hTail :
              HeadGoalFiresCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal (.imp u v) 0 a)
                (.atom a) := by
            rw [headGoalFiresCtx_iff_firesCtx]
            simpa [encodeBase] using
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .imp u v)
                (a := a) (fuel := fuel) hFireD).2
          have hGoal : GoalSupports P (encode φ) :=
            hAmbientAllImpImp haEncodeφ haP hDP hFireD hPrem hTail
          rw [goalSupports_iff_search] at hGoal
          exact hGoal
        · rcases hAll with ⟨u, rfl⟩
          have hPrem :
              HeadGoalSupportsCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal g₁ 0 a) :=
            derives_to_headGoalSupportsCtx_singleton <|
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .all u)
                (a := a) (fuel := fuel) hFireD).1
          have hTail :
              HeadGoalFiresCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal (.all u) 0 a)
                (.atom a) := by
            rw [headGoalFiresCtx_iff_firesCtx]
            simpa [encodeBase] using
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .all u)
                (a := a) (fuel := fuel) hFireD).2
          have hGoal : GoalSupports P (encode φ) :=
            hAmbientAllImpAll haEncodeφ haP hDP hFireD hPrem hTail
          rw [goalSupports_iff_search] at hGoal
          exact hGoal)
    (fun {a} {g} {fuel} haEncodeφ haP hDP hFireD =>
      by
        have hTail :
            HeadGoalFiresCtx
              [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
              P
              (substGoal (substGoal g 1 a) 0 a)
              (.atom a) := by
          rw [headGoalFiresCtx_iff_firesCtx]
          simpa [encodeBase] using
            cps_conj_ambient_all_all_fire_case
              (P := P) φ ψ (g := g) (a := a) (fuel := fuel) hFireD
        have hGoal : GoalSupports P (encode φ) :=
          hAmbientAllAll haEncodeφ haP hDP hFireD hTail
        rw [goalSupports_iff_search] at hGoal
        exact hGoal)
    h

theorem cps_conj_extract_left_from_fresh_body_of_ambient_all_imp_root_cases_in_head_context
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeφ : a ∉ goalAtoms (encode φ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hAmbientImp :
      ∀ {g₁ g₂ : Goal} {fuel : Nat},
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode φ))
    (hAmbientAllImpTopAtom :
      ∀ {v : AtomVar} {fuel : Nat},
        Goal.all (.imp (.atom v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.atom v) (.atom (.bvar 0))))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode φ))
    (hAmbientAllImpTopImp :
      ∀ {u v : Goal} {fuel : Nat},
        Goal.all (.imp (.imp u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.imp u v) (.atom (.bvar 0))))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode φ))
    (hAmbientAllImpTopDisj :
      ∀ {u v : Goal} {fuel : Nat},
        Goal.all (.imp (.disj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.disj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode φ))
    (hAmbientAllImpTopConj :
      ∀ {u v : Goal} {fuel : Nat},
        Goal.all (.imp (.conj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.conj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode φ))
    (hAmbientAllImpTopAll :
      ∀ {u : Goal} {fuel : Nat},
        Goal.all (.imp (.all u) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.all u) (.atom (.bvar 0))))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode φ))
    (hAmbientAllImpImp :
      ∀ {g₁ u v : Goal} {fuel : Nat},
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode φ))
    (hAmbientAllImpAll :
      ∀ {g₁ u : Goal} {fuel : Nat},
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode φ))
    (hAmbientAllAll :
      ∀ {g : Goal} {fuel : Nat},
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode φ)) :
    Derives
      (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
      (encode φ) := by
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have hSearchP : SearchSupports P (encode φ) := by
    exact cps_conj_extract_left_from_fresh_body_of_ambient_all_member_cases
      φ ψ haEncodeφ haP hSub
      (fun {g₁} {g₂} {fuel} hDP hFireD =>
        cps_conj_head_context_derives_to_ambient_search
          (φ := φ) (ψ := ψ) (χ := φ) (a := a) haEncodeφ haP <|
          hAmbientImp hDP hFireD)
      (fun {g₁} {g₂} {fuel} hDP hFireD => by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          cases g₁ with
          | atom v =>
              exact cps_conj_head_context_derives_to_ambient_search
                (φ := φ) (ψ := ψ) (χ := φ) (a := a) haEncodeφ haP <|
                hAmbientAllImpTopAtom hDP hFireD
          | imp u v =>
              exact cps_conj_head_context_derives_to_ambient_search
                (φ := φ) (ψ := ψ) (χ := φ) (a := a) haEncodeφ haP <|
                hAmbientAllImpTopImp hDP hFireD
          | conj u v =>
              exact cps_conj_head_context_derives_to_ambient_search
                (φ := φ) (ψ := ψ) (χ := φ) (a := a) haEncodeφ haP <|
                hAmbientAllImpTopConj hDP hFireD
          | disj u v =>
              exact cps_conj_head_context_derives_to_ambient_search
                (φ := φ) (ψ := ψ) (χ := φ) (a := a) haEncodeφ haP <|
                hAmbientAllImpTopDisj hDP hFireD
          | all u =>
              exact cps_conj_head_context_derives_to_ambient_search
                (φ := φ) (ψ := ψ) (χ := φ) (a := a) haEncodeφ haP <|
                hAmbientAllImpTopAll hDP hFireD
        · rcases hImp with ⟨u, v, rfl⟩
          exact cps_conj_head_context_derives_to_ambient_search
            (φ := φ) (ψ := ψ) (χ := φ) (a := a) haEncodeφ haP <|
            hAmbientAllImpImp hDP hFireD
        · rcases hAll with ⟨u, rfl⟩
          exact cps_conj_head_context_derives_to_ambient_search
            (φ := φ) (ψ := ψ) (χ := φ) (a := a) haEncodeφ haP <|
            hAmbientAllImpAll hDP hFireD)
      (fun {g} {fuel} hDP hFireD =>
        cps_conj_head_context_derives_to_ambient_search
          (φ := φ) (ψ := ψ) (χ := φ) (a := a) haEncodeφ haP <|
          hAmbientAllAll hDP hFireD)
  exact derives_weaken (extras := [K]) <| derives_iff_searchSupports.mpr hSearchP

theorem cps_conj_extract_left_of_all_body_obstruction
    {P : Program} (φ ψ : IPL)
    (hAllBody :
      ∀ {a : Atom} {body : Goal},
        a ∉ goalAtoms (encode φ) →
        a ∉ programAtoms P →
        a ∉ goalAtoms body →
        Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (substGoal body 0 a)
          (.atom a) →
        SearchSupports P (encode φ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode φ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeφ : a ∉ goalAtoms (encode φ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_left_from_fresh_body_of_all_body_obstruction φ ψ haEncodeφ haP hSub'
    (fun {body} haBody hBodyFire => hAllBody haEncodeφ haP haBody hBodyFire)

theorem cps_conj_extract_right_of_head_search
    {P : Program} (φ ψ : IPL)
    (hHeadSearch :
      ∀ {a : Atom} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode ψ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeψ : a ∉ goalAtoms (encode ψ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_right_from_fresh_body_of_resolution φ ψ haEncodeψ haP hSub'
    (fun {fuel} hAny => Or.inl (hHeadSearch haEncodeψ haP hAny))

theorem cps_conj_extract_right_of_resolution
    {P : Program} (φ ψ : IPL)
    (hResolve :
      ∀ {a : Atom} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        searchAnyAssumption fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.atom a) = true →
          fires fuel
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
            (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (.atom a) = true ∨
            SearchSupports P (encode ψ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode ψ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeψ : a ∉ goalAtoms (encode ψ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_right_from_fresh_body_of_resolution φ ψ haEncodeψ haP hSub'
    (fun {fuel} hAny => hResolve haEncodeψ haP hAny)

theorem cps_conj_extract_right_of_ambient_clause
    {P : Program} (φ ψ : IPL)
    (hAmbient :
      ∀ {a : Atom} {D : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        D ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          D
          (.atom a) = true →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode ψ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeψ : a ∉ goalAtoms (encode ψ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_right_from_fresh_body_of_ambient_clause φ ψ haEncodeψ haP hSub'
    (fun {D} {fuel} hDP hFireD => hAmbient haEncodeψ haP hDP hFireD)

theorem cps_conj_extract_right_of_ambient_constructor_cases
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all g ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all g)
          (.atom a) = true →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode ψ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeψ : a ∉ goalAtoms (encode ψ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_right_from_fresh_body_of_ambient_constructor_cases φ ψ haEncodeψ haP hSub'
    (fun {g₁} {g₂} {fuel} hDP hFireD => hAmbientImp haEncodeψ haP hDP hFireD)
    (fun {g} {fuel} hDP hFireD => hAmbientAll haEncodeψ haP hDP hFireD)

theorem cps_conj_extract_right_of_ambient_all_member_cases
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ g₂) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ g₂))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode ψ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeψ : a ∉ goalAtoms (encode ψ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' : Derives P (.imp K (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_right_from_fresh_body_of_ambient_all_member_cases φ ψ haEncodeψ haP hSub'
    (fun {g₁} {g₂} {fuel} hDP hFireD => hAmbientImp haEncodeψ haP hDP hFireD)
    (fun {g₁} {g₂} {fuel} hDP hFireD => hAmbientAllImp haEncodeψ haP hDP hFireD)
    (fun {g} {fuel} hDP hFireD => hAmbientAllAll haEncodeψ haP hDP hFireD)

theorem cps_conj_extract_right_of_ambient_all_imp_tail_cases
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpTop :
      ∀ {a : Atom} {g₁ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode ψ) := by
  intro h
  exact cps_conj_extract_right_of_ambient_all_member_cases (P := P) φ ψ
    hAmbientImp
    (fun {a} {g₁} {g₂} {fuel} haEncodeψ haP hDP hFireD =>
      by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          exact hAmbientAllImpTop haEncodeψ haP hDP hFireD
        · rcases hImp with ⟨u, v, rfl⟩
          exact hAmbientAllImpImp haEncodeψ haP hDP hFireD
        · rcases hAll with ⟨u, rfl⟩
          exact hAmbientAllImpAll haEncodeψ haP hDP hFireD)
    hAmbientAllAll
    h

theorem cps_conj_extract_right_of_ambient_all_imp_root_cases
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpTopAtom :
      ∀ {a : Atom} {v : AtomVar} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.atom v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.atom v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpTopImp :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.imp u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.imp u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpTopDisj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.disj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.disj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpTopConj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.conj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.conj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpTopAll :
      ∀ {a : Atom} {u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.all u) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.all u) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode ψ) := by
  intro h
  exact cps_conj_extract_right_of_ambient_all_member_cases (P := P) φ ψ
    hAmbientImp
    (fun {a} {g₁} {g₂} {fuel} haEncodeψ haP hDP hFireD =>
      by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          rcases cps_conj_ambient_all_imp_top_member_focused_cases
              (P := P) φ ψ (prem := g₁) (a := a) (fuel := fuel)
              hDP haP hFireD with
            hAtom | hConj | hImpRoot | hDisj | hAllRoot
          · rcases hAtom with ⟨v, rfl⟩
            exact hAmbientAllImpTopAtom haEncodeψ haP hDP hFireD
          · rcases hConj with ⟨u, v, rfl, _hDu, _hDv⟩
            exact hAmbientAllImpTopConj haEncodeψ haP hDP hFireD
          · rcases hImpRoot with ⟨u, v, rfl⟩
            exact hAmbientAllImpTopImp haEncodeψ haP hDP hFireD
          · rcases hDisj with ⟨u, v, rfl⟩
            exact hAmbientAllImpTopDisj haEncodeψ haP hDP hFireD
          · rcases hAllRoot with ⟨u, rfl⟩
            exact hAmbientAllImpTopAll haEncodeψ haP hDP hFireD
        · rcases hImp with ⟨u, v, rfl⟩
          exact hAmbientAllImpImp haEncodeψ haP hDP hFireD
        · rcases hAll with ⟨u, rfl⟩
          exact hAmbientAllImpAll haEncodeψ haP hDP hFireD)
    hAmbientAllAll
    h

/--
Right conjunction extraction with the residual top-`conj` callback lifted into
the goal-level semantic surface.

Only the `prem = conj _ _` branch is changed: the callback now consumes the two
instantiated conjunct supports in the head context `K :: P` and returns an
ambient `GoalSupports` conclusion.
-/
theorem cps_conj_extract_right_of_ambient_all_imp_root_cases_goal_top_conj
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpTopAtom :
      ∀ {a : Atom} {v : AtomVar} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.atom v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.atom v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpTopImp :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.imp u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.imp u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpTopDisj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.disj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.disj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpTopConj :
      ∀ {a : Atom} {u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.conj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.conj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal u 0 a) →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal v 0 a) →
        GoalSupports P (encode ψ))
    (hAmbientAllImpTopAll :
      ∀ {a : Atom} {u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp (.all u) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.all u) (.atom (.bvar 0))))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode ψ) := by
  intro h
  exact cps_conj_extract_right_of_ambient_all_member_cases (P := P) φ ψ
    hAmbientImp
    (fun {a} {g₁} {g₂} {fuel} haEncodeψ haP hDP hFireD =>
      by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          rcases cps_conj_ambient_all_imp_top_member_focused_cases
              (P := P) φ ψ (prem := g₁) (a := a) (fuel := fuel)
              hDP haP hFireD with
            hAtom | hConj | hImpRoot | hDisj | hAllRoot
          · rcases hAtom with ⟨v, rfl⟩
            exact hAmbientAllImpTopAtom haEncodeψ haP hDP hFireD
          · rcases hConj with ⟨u, v, rfl, hDu, hDv⟩
            have hTopU :
                HeadGoalSupportsCtx
                  [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                  P
                  (substGoal u 0 a) :=
              derives_to_headGoalSupportsCtx_singleton hDu
            have hTopV :
                HeadGoalSupportsCtx
                  [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                  P
                  (substGoal v 0 a) :=
              derives_to_headGoalSupportsCtx_singleton hDv
            have hGoal :
                GoalSupports P (encode ψ) :=
              hAmbientAllImpTopConj haEncodeψ haP hDP hFireD hTopU hTopV
            rw [goalSupports_iff_search] at hGoal
            exact hGoal
          · rcases hImpRoot with ⟨u, v, rfl⟩
            exact hAmbientAllImpTopImp haEncodeψ haP hDP hFireD
          · rcases hDisj with ⟨u, v, rfl⟩
            exact hAmbientAllImpTopDisj haEncodeψ haP hDP hFireD
          · rcases hAllRoot with ⟨u, rfl⟩
            exact hAmbientAllImpTopAll haEncodeψ haP hDP hFireD
        · rcases hImp with ⟨u, v, rfl⟩
          exact hAmbientAllImpImp haEncodeψ haP hDP hFireD
        · rcases hAll with ⟨u, rfl⟩
          exact hAmbientAllImpAll haEncodeψ haP hDP hFireD)
    hAmbientAllAll
    h

/--
Right conjunction extraction with the entire top-tail `∀X.(prem -> X)` family
lifted into the goal-level semantic surface.

Whenever the ambient member has tail `atom (bvar 0)`, the Bridge layer derives
the instantiated premise in `K :: P`, packages it as `HeadGoalSupportsCtx [K] P`,
and hands it to a single semantic callback.
-/
theorem cps_conj_extract_right_of_ambient_all_imp_root_cases_goal_top
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpTop :
      ∀ {a : Atom} {prem : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp prem (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp prem (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal prem 0 a) →
        GoalSupports P (encode ψ))
    (hAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        SearchSupports P (encode ψ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode ψ) := by
  intro h
  exact cps_conj_extract_right_of_ambient_all_member_cases (P := P) φ ψ
    hAmbientImp
    (fun {a} {g₁} {g₂} {fuel} haEncodeψ haP hDP hFireD =>
      by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          have hPrem :
              HeadGoalSupportsCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal g₁ 0 a) :=
            derives_to_headGoalSupportsCtx_singleton <|
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .atom (.bvar 0))
                (a := a) (fuel := fuel) hFireD).1
          have hGoal : GoalSupports P (encode ψ) :=
            hAmbientAllImpTop haEncodeψ haP hDP hFireD hPrem
          rw [goalSupports_iff_search] at hGoal
          exact hGoal
        · rcases hImp with ⟨u, v, rfl⟩
          exact hAmbientAllImpImp haEncodeψ haP hDP hFireD
        · rcases hAll with ⟨u, rfl⟩
          exact hAmbientAllImpAll haEncodeψ haP hDP hFireD)
    hAmbientAllAll
    h

/--
Right conjunction extraction with the surviving recursive ambient tail
callbacks lifted into the mixed goal-support / goal-fire semantic surface.
-/
theorem cps_conj_extract_right_of_ambient_all_imp_root_cases_goal_fire
    {P : Program} (φ ψ : IPL)
    (hAmbientImp :
      ∀ {a : Atom} {g₁ g₂ : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          g₁ →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          g₂
          (.atom a) →
        GoalSupports P (encode ψ))
    (hAmbientAllImpTop :
      ∀ {a : Atom} {prem : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp prem (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp prem (.atom (.bvar 0))))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal prem 0 a) →
        GoalSupports P (encode ψ))
    (hAmbientAllImpImp :
      ∀ {a : Atom} {g₁ u v : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal g₁ 0 a) →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal (.imp u v) 0 a)
          (.atom a) →
        GoalSupports P (encode ψ))
    (hAmbientAllImpAll :
      ∀ {a : Atom} {g₁ u : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        HeadGoalSupportsCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal g₁ 0 a) →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal (.all u) 0 a)
          (.atom a) →
        GoalSupports P (encode ψ))
    (hAmbientAllAll :
      ∀ {a : Atom} {g : Goal} {fuel : Nat},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        HeadGoalFiresCtx
          [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
          P
          (substGoal (substGoal g 1 a) 0 a)
          (.atom a) →
        GoalSupports P (encode ψ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode ψ) := by
  intro h
  exact cps_conj_extract_right_of_ambient_all_member_cases (P := P) φ ψ
    (fun {a} {g₁} {g₂} {fuel} haEncodeψ haP hDP hFireD =>
      by
        rcases fires_imp_to_headGoalSupportsCtx_and_headGoalFires
            (P := P)
            (K := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
            (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hFireD with
          ⟨hPrem, hTail⟩
        have hGoal : GoalSupports P (encode ψ) :=
          hAmbientImp haEncodeψ haP hDP hFireD hPrem hTail
        rw [goalSupports_iff_search] at hGoal
        exact hGoal)
    (fun {a} {g₁} {g₂} {fuel} haEncodeψ haP hDP hFireD =>
      by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          have hPrem :
              HeadGoalSupportsCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal g₁ 0 a) :=
            derives_to_headGoalSupportsCtx_singleton <|
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .atom (.bvar 0))
                (a := a) (fuel := fuel) hFireD).1
          have hGoal : GoalSupports P (encode ψ) :=
            hAmbientAllImpTop haEncodeψ haP hDP hFireD hPrem
          rw [goalSupports_iff_search] at hGoal
          exact hGoal
        · rcases hImp with ⟨u, v, rfl⟩
          have hPrem :
              HeadGoalSupportsCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal g₁ 0 a) :=
            derives_to_headGoalSupportsCtx_singleton <|
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .imp u v)
                (a := a) (fuel := fuel) hFireD).1
          have hTail :
              HeadGoalFiresCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal (.imp u v) 0 a)
                (.atom a) := by
            rw [headGoalFiresCtx_iff_firesCtx]
            simpa [encodeBase] using
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .imp u v)
                (a := a) (fuel := fuel) hFireD).2
          have hGoal : GoalSupports P (encode ψ) :=
            hAmbientAllImpImp haEncodeψ haP hDP hFireD hPrem hTail
          rw [goalSupports_iff_search] at hGoal
          exact hGoal
        · rcases hAll with ⟨u, rfl⟩
          have hPrem :
              HeadGoalSupportsCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal g₁ 0 a) :=
            derives_to_headGoalSupportsCtx_singleton <|
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .all u)
                (a := a) (fuel := fuel) hFireD).1
          have hTail :
              HeadGoalFiresCtx
                [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
                P
                (substGoal (.all u) 0 a)
                (.atom a) := by
            rw [headGoalFiresCtx_iff_firesCtx]
            simpa [encodeBase] using
              (cps_conj_ambient_all_imp_fire_cases
                (P := P) φ ψ (g₁ := g₁) (g₂ := .all u)
                (a := a) (fuel := fuel) hFireD).2
          have hGoal : GoalSupports P (encode ψ) :=
            hAmbientAllImpAll haEncodeψ haP hDP hFireD hPrem hTail
          rw [goalSupports_iff_search] at hGoal
          exact hGoal)
    (fun {a} {g} {fuel} haEncodeψ haP hDP hFireD =>
      by
        have hTail :
            HeadGoalFiresCtx
              [.imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))]
              P
              (substGoal (substGoal g 1 a) 0 a)
              (.atom a) := by
          rw [headGoalFiresCtx_iff_firesCtx]
          simpa [encodeBase] using
            cps_conj_ambient_all_all_fire_case
              (P := P) φ ψ (g := g) (a := a) (fuel := fuel) hFireD
        have hGoal : GoalSupports P (encode ψ) :=
          hAmbientAllAll haEncodeψ haP hDP hFireD hTail
        rw [goalSupports_iff_search] at hGoal
        exact hGoal)
    h

theorem cps_conj_extract_right_from_fresh_body_of_ambient_all_imp_root_cases_in_head_context
    {P : Program} (φ ψ : IPL) {a : Atom}
    (haEncodeψ : a ∉ goalAtoms (encode ψ))
    (haP : a ∉ programAtoms P)
    (hSub :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))))
    (hAmbientImp :
      ∀ {g₁ g₂ : Goal} {fuel : Nat},
        Goal.imp g₁ g₂ ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.imp g₁ g₂)
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode ψ))
    (hAmbientAllImpTopAtom :
      ∀ {v : AtomVar} {fuel : Nat},
        Goal.all (.imp (.atom v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.atom v) (.atom (.bvar 0))))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode ψ))
    (hAmbientAllImpTopImp :
      ∀ {u v : Goal} {fuel : Nat},
        Goal.all (.imp (.imp u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.imp u v) (.atom (.bvar 0))))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode ψ))
    (hAmbientAllImpTopDisj :
      ∀ {u v : Goal} {fuel : Nat},
        Goal.all (.imp (.disj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.disj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode ψ))
    (hAmbientAllImpTopConj :
      ∀ {u v : Goal} {fuel : Nat},
        Goal.all (.imp (.conj u v) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.conj u v) (.atom (.bvar 0))))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode ψ))
    (hAmbientAllImpTopAll :
      ∀ {u : Goal} {fuel : Nat},
        Goal.all (.imp (.all u) (.atom (.bvar 0))) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp (.all u) (.atom (.bvar 0))))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode ψ))
    (hAmbientAllImpImp :
      ∀ {g₁ u v : Goal} {fuel : Nat},
        Goal.all (.imp g₁ (.imp u v)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.imp u v)))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode ψ))
    (hAmbientAllImpAll :
      ∀ {g₁ u : Goal} {fuel : Nat},
        Goal.all (.imp g₁ (.all u)) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.imp g₁ (.all u)))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode ψ))
    (hAmbientAllAll :
      ∀ {g : Goal} {fuel : Nat},
        Goal.all (.all g) ∈ P →
        fires fuel
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (.all (.all g))
          (.atom a) = true →
        Derives
          (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (encode ψ)) :
    Derives
      (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
      (encode ψ) := by
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have hSearchP : SearchSupports P (encode ψ) := by
    exact cps_conj_extract_right_from_fresh_body_of_ambient_all_member_cases
      φ ψ haEncodeψ haP hSub
      (fun {g₁} {g₂} {fuel} hDP hFireD =>
        cps_conj_head_context_derives_to_ambient_search
          (φ := φ) (ψ := ψ) (χ := ψ) (a := a) haEncodeψ haP <|
          hAmbientImp hDP hFireD)
      (fun {g₁} {g₂} {fuel} hDP hFireD => by
        rcases cps_conj_ambient_all_imp_tail_fresh_atom_cases
            (P := P) φ ψ (g₁ := g₁) (g₂ := g₂) (a := a) (fuel := fuel) hDP haP hFireD with
          hTop | hImp | hAll
        · subst hTop
          cases g₁ with
          | atom v =>
              exact cps_conj_head_context_derives_to_ambient_search
                (φ := φ) (ψ := ψ) (χ := ψ) (a := a) haEncodeψ haP <|
                hAmbientAllImpTopAtom hDP hFireD
          | imp u v =>
              exact cps_conj_head_context_derives_to_ambient_search
                (φ := φ) (ψ := ψ) (χ := ψ) (a := a) haEncodeψ haP <|
                hAmbientAllImpTopImp hDP hFireD
          | conj u v =>
              exact cps_conj_head_context_derives_to_ambient_search
                (φ := φ) (ψ := ψ) (χ := ψ) (a := a) haEncodeψ haP <|
                hAmbientAllImpTopConj hDP hFireD
          | disj u v =>
              exact cps_conj_head_context_derives_to_ambient_search
                (φ := φ) (ψ := ψ) (χ := ψ) (a := a) haEncodeψ haP <|
                hAmbientAllImpTopDisj hDP hFireD
          | all u =>
              exact cps_conj_head_context_derives_to_ambient_search
                (φ := φ) (ψ := ψ) (χ := ψ) (a := a) haEncodeψ haP <|
                hAmbientAllImpTopAll hDP hFireD
        · rcases hImp with ⟨u, v, rfl⟩
          exact cps_conj_head_context_derives_to_ambient_search
            (φ := φ) (ψ := ψ) (χ := ψ) (a := a) haEncodeψ haP <|
            hAmbientAllImpImp hDP hFireD
        · rcases hAll with ⟨u, rfl⟩
          exact cps_conj_head_context_derives_to_ambient_search
            (φ := φ) (ψ := ψ) (χ := ψ) (a := a) haEncodeψ haP <|
            hAmbientAllImpAll hDP hFireD)
      (fun {g} {fuel} hDP hFireD =>
        cps_conj_head_context_derives_to_ambient_search
          (φ := φ) (ψ := ψ) (χ := ψ) (a := a) haEncodeψ haP <|
          hAmbientAllAll hDP hFireD)
  exact derives_weaken (extras := [K]) <| derives_iff_searchSupports.mpr hSearchP

theorem cps_conj_extract_right_of_all_body_obstruction
    {P : Program} (φ ψ : IPL)
    (hAllBody :
      ∀ {a : Atom} {body : Goal},
        a ∉ goalAtoms (encode ψ) →
        a ∉ programAtoms P →
        a ∉ goalAtoms body →
        Fires (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))) :: P)
          (substGoal body 0 a)
          (.atom a) →
        SearchSupports P (encode ψ)) :
    SearchSupports P (encode (.conj φ ψ)) →
      SearchSupports P (encode ψ) := by
  intro h
  have hD : Derives P (encode (.conj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  rcases derives_all_inversion hD with ⟨a, haP, haBody, hSub⟩
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  have haEncodeψ : a ∉ goalAtoms (encode ψ) := by
    intro hm
    exact haBody (by simp [goalAtoms, hm])
  have hSub' :
      Derives P
        (.imp (.imp (encode φ) (.imp (encode ψ) (.atom (.atom a))))
          (.atom (.atom a))) := by
    simpa [K, substGoal, substGoal_encode] using hSub
  exact cps_conj_extract_right_from_fresh_body_of_all_body_obstruction φ ψ haEncodeψ haP hSub'
    (fun {body} haBody hBodyFire => hAllBody haEncodeψ haP haBody hBodyFire)

theorem cps_conj_extract_left (atoms : List Atom) (φ ψ : IPL) :
    SearchSupports (atomicBase atoms) (encode (.conj φ ψ)) →
      SearchSupports (atomicBase atoms) (encode φ) := by
  refine cps_conj_extract_left_of_head_search (P := atomicBase atoms) φ ψ ?_
  intro a fuel haEncodeφ haP hAny
  have haB : a ∉ atoms := by
    rw [← programAtoms_atomicBase atoms]
    exact haP
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  exact searchAnyAssumption_atomicBase_fresh_atom_from_head
    (fuel := fuel) (atoms := atoms) (K := K) (a := a) haB hAny

theorem cps_conj_extract_right (atoms : List Atom) (φ ψ : IPL) :
    SearchSupports (atomicBase atoms) (encode (.conj φ ψ)) →
      SearchSupports (atomicBase atoms) (encode ψ) := by
  refine cps_conj_extract_right_of_head_search (P := atomicBase atoms) φ ψ ?_
  intro a fuel haEncodeψ haP hAny
  have haB : a ∉ atoms := by
    rw [← programAtoms_atomicBase atoms]
    exact haP
  let K : Goal := .imp (encode φ) (.imp (encode ψ) (.atom (.atom a)))
  exact searchAnyAssumption_atomicBase_fresh_atom_from_head
    (fuel := fuel) (atoms := atoms) (K := K) (a := a) haB hAny

theorem cps_disj_extract (atoms : List Atom) (φ ψ : IPL) :
    SearchSupports (atomicBase atoms) (encode (.disj φ ψ)) →
    SearchSupports (atomicBase atoms) (encode φ) ∨
      SearchSupports (atomicBase atoms) (encode ψ) := by
  intro h
  have hD : Derives (atomicBase atoms) (encode (.disj φ ψ)) :=
    derives_iff_searchSupports.mpr h
  cases hD with
  | all a haP haBody hSub =>
      let Kφ : Goal := .imp (encode φ) (.atom (.atom a))
      let Kψ : Goal := .imp (encode ψ) (.atom (.atom a))
      have haB : a ∉ atoms := by
        rw [← programAtoms_atomicBase atoms]
        exact haP
      have haEncodeφ : a ∉ goalAtoms (encode φ) := by
        intro hm
        exact haBody (by simp [goalAtoms, hm])
      have haEncodeψ : a ∉ goalAtoms (encode ψ) := by
        intro hm
        exact haBody (by simp [goalAtoms, hm])
      have haP' : a ∉ programAtoms (atomicBase atoms) := by
        rw [programAtoms_atomicBase]
        exact haB
      have hSub' :
          Derives (atomicBase atoms)
            (.imp Kφ (.imp Kψ (.atom (.atom a)))) := by
        simpa [Kφ, Kψ, substGoal, substGoal_encode] using hSub
      have hAtom' : Derives (Kψ :: Kφ :: atomicBase atoms) (.atom (.atom a)) :=
        cps_disj_atom_from_sub hSub'
      rcases derives_to_search hAtom' with ⟨fuel, hfuel⟩
      cases fuel with
      | zero =>
          simp [search] at hfuel
      | succ fuel =>
          have hHeadBool :
              fires fuel (Kψ :: Kφ :: atomicBase atoms) Kψ (.atom a) = true ∨
                fires fuel (Kψ :: Kφ :: atomicBase atoms) Kφ (.atom a) = true := by
            apply searchAnyAssumption_atomicBase_fresh_atom_from_two_heads
              (fuel := fuel) (atoms := atoms) (Kφ := Kφ) (Kψ := Kψ) (a := a) haB
            simpa [search] using hfuel
          rcases hHeadBool with hKψ | hKφ
          · have hψDer : Derives (Kψ :: Kφ :: atomicBase atoms) (encode ψ) :=
              cps_disj_right_from_head (a := a) <|
                by simpa [Kψ] using fires_to_derives hKψ
            rcases derives_to_search hψDer with ⟨fuelψ, hfuelψ⟩
            exact Or.inr ⟨fuelψ, search_strengthen_two_fresh_heads
              (haKφ := by simp [Kφ, goalAtoms, atomVarAtoms])
              (haKψ := by simp [Kψ, goalAtoms, atomVarAtoms])
              (hKφ_fires_only_a := by
                intro P v hF
                exact cps_disj_K_fires_only_for (χ := φ) (a := a) hF)
              (hKψ_fires_only_a := by
                intro P v hF
                exact cps_disj_K_fires_only_for (χ := ψ) (a := a) hF)
              fuelψ (atomicBase atoms) (encode ψ) haEncodeψ haP' hfuelψ⟩
          · have hφDer : Derives (Kψ :: Kφ :: atomicBase atoms) (encode φ) :=
              cps_disj_left_from_head (a := a) <|
                by simpa [Kφ] using fires_to_derives hKφ
            rcases derives_to_search hφDer with ⟨fuelφ, hfuelφ⟩
            exact Or.inl ⟨fuelφ, search_strengthen_two_fresh_heads
              (haKφ := by simp [Kφ, goalAtoms, atomVarAtoms])
              (haKψ := by simp [Kψ, goalAtoms, atomVarAtoms])
              (hKφ_fires_only_a := by
                intro P v hF
                exact cps_disj_K_fires_only_for (χ := φ) (a := a) hF)
              (hKψ_fires_only_a := by
                intro P v hF
                exact cps_disj_K_fires_only_for (χ := ψ) (a := a) hF)
              fuelφ (atomicBase atoms) (encode φ) haEncodeφ haP' hfuelφ⟩

theorem atomicBase_search_bot_false (atoms : List Atom) :
    ¬ SearchSupports (atomicBase atoms) (encode .bot) := by
  intro ⟨fuel, hfuel⟩
  cases fuel with
  | zero => simp [search] at hfuel
  | succ fuel =>
      -- encode .bot = all (atom (bvar 0))
      -- search (fuel+1) P (all g) = search fuel P (substGoal (atom (bvar 0)) 0 fresh)
      -- = search fuel P (atom (.atom fresh))
      simp only [encode, search, substGoal, substAtomVar] at hfuel
      -- hfuel : search fuel (atomicBase atoms) (atom (.atom (freshAtomForGoal ...))) = true
      -- This means the fresh atom is searchable, so by atom bridge it's in atoms
      have hmem := (atomicBase_search_atom_iff atoms _).mp ⟨fuel, hfuel⟩
      exact freshAtomForGoal_not_in_atomicBase atoms _ hmem

-- Legacy alias
theorem encodeBase_search_bot_false (atoms : List Atom) :
    ¬ SearchSupports (atomicBase atoms) (encode .bot) :=
  atomicBase_search_bot_false atoms

theorem search_cut_bot (atoms : List Atom) (ψ : IPL) :
    SearchSupports (atomicBase atoms) (encode .bot) →
    SearchSupports (encode .bot :: atomicBase atoms) (encode ψ) →
    SearchSupports (atomicBase atoms) (encode ψ) := by
  intro hBot
  exact False.elim (atomicBase_search_bot_false atoms hBot)

/-- Disjunction forward: from semantic disjunction support (elimination principle),
    derive CPS search. Paper Theorem 4.6, disjunction forward.
    The CPS encoding ∀X.((⟦φ⟧→X)→(⟦ψ⟧→X)→X) captures the elimination principle. -/
private theorem disj_search_of_left (B : Base) (φ ψ : IPL) :
    SearchSupports (encodeBase B) (encode φ) →
    SearchSupports (encodeBase B) (encode (.disj φ ψ)) := by
  intro hφ
  rcases hφ with ⟨fuel, hfuel⟩
  let P := encodeBase B
  let body : Goal :=
    Goal.imp
      (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
      (Goal.imp
        (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
        (Goal.atom (.bvar 0)))
  let c := freshAtomForGoal P body
  let Kφ : Goal := Goal.imp (encode φ) (Goal.atom (.atom c))
  let Kψ : Goal := Goal.imp (encode ψ) (Goal.atom (.atom c))
  let P' : Program := Kψ :: Kφ :: P
  have hφ_w : search fuel P' (encode φ) = true := by
    simpa [P', Kφ, Kψ] using search_weaken fuel P [Kψ, Kφ] (encode φ) hfuel
  have hφ_w1 : search (fuel + 1) P' (encode φ) = true :=
    search_fuel_mono fuel 1 P' (encode φ) hφ_w
  have hc_fires : fires (fuel + 1) P' (.atom (.atom c)) (.atom c) = true := by
    have : fuel + 1 = fuel.succ := by omega
    rw [this, fires.eq_2]
    simp
  have hKφ_fires : fires (fuel + 2) P' Kφ (.atom c) = true := by
    have : fuel + 2 = (fuel + 1).succ := by omega
    rw [this, fires.eq_3, Bool.and_eq_true]
    exact ⟨hφ_w1, hc_fires⟩
  have hSAA_tail : searchAnyAssumption (fuel + 2) P' (Kφ :: P) (.atom c) = true := by
    simp [searchAnyAssumption, hKφ_fires]
  have hSAA : searchAnyAssumption (fuel + 2) P' P' (.atom c) = true := by
    simp [P', searchAnyAssumption, hSAA_tail]
  refine ⟨fuel + 6, ?_⟩
  have h6 : fuel + 6 = (fuel + 5).succ := by omega
  have h5 : fuel + 5 = (fuel + 4).succ := by omega
  have h4 : fuel + 4 = (fuel + 3).succ := by omega
  have h3 : fuel + 3 = (fuel + 2).succ := by omega
  rw [encode, h6, search.eq_6]
  simp only [substGoal, substAtomVar, substGoal_encode]
  rw [h5, search.eq_3, h4, search.eq_3, h3, search.eq_2]
  exact hSAA

private theorem disj_search_of_right (B : Base) (φ ψ : IPL) :
    SearchSupports (encodeBase B) (encode ψ) →
    SearchSupports (encodeBase B) (encode (.disj φ ψ)) := by
  intro hψ
  rcases hψ with ⟨fuel, hfuel⟩
  let P := encodeBase B
  let body : Goal :=
    Goal.imp
      (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
      (Goal.imp
        (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
        (Goal.atom (.bvar 0)))
  let c := freshAtomForGoal P body
  let Kφ : Goal := Goal.imp (encode φ) (Goal.atom (.atom c))
  let Kψ : Goal := Goal.imp (encode ψ) (Goal.atom (.atom c))
  let P' : Program := Kψ :: Kφ :: P
  have hψ_w : search fuel P' (encode ψ) = true := by
    simpa [P', Kφ, Kψ] using search_weaken fuel P [Kψ, Kφ] (encode ψ) hfuel
  have hψ_w1 : search (fuel + 1) P' (encode ψ) = true :=
    search_fuel_mono fuel 1 P' (encode ψ) hψ_w
  have hc_fires : fires (fuel + 1) P' (.atom (.atom c)) (.atom c) = true := by
    have : fuel + 1 = fuel.succ := by omega
    rw [this, fires.eq_2]
    simp
  have hKψ_fires : fires (fuel + 2) P' Kψ (.atom c) = true := by
    have : fuel + 2 = (fuel + 1).succ := by omega
    rw [this, fires.eq_3, Bool.and_eq_true]
    exact ⟨hψ_w1, hc_fires⟩
  have hSAA : searchAnyAssumption (fuel + 2) P' P' (.atom c) = true := by
    simp [P', searchAnyAssumption, hKψ_fires]
  refine ⟨fuel + 6, ?_⟩
  have h6 : fuel + 6 = (fuel + 5).succ := by omega
  have h5 : fuel + 5 = (fuel + 4).succ := by omega
  have h4 : fuel + 4 = (fuel + 3).succ := by omega
  have h3 : fuel + 3 = (fuel + 2).succ := by omega
  rw [encode, h6, search.eq_6]
  simp only [substGoal, substAtomVar, substGoal_encode]
  rw [h5, search.eq_3, h4, search.eq_3, h3, search.eq_2]
  exact hSAA

/-- Disjunction forward for atomic bases (elimination-style semantics). -/
theorem disj_forward_axiom (atoms : List Atom) (φ ψ : IPL) :
    (∀ C : List Atom, (∀ a, a ∈ atoms → a ∈ C) → ∀ p : Atom,
      (SearchSupports (atomicBase C) (encode φ) → p ∈ C) →
      (SearchSupports (atomicBase C) (encode ψ) → p ∈ C) →
      p ∈ C) →
    SearchSupports (atomicBase atoms) (encode (.disj φ ψ)) := by
  classical
  intro h
  let P := atomicBase atoms
  let body : Goal :=
    Goal.imp
      (Goal.imp (encode φ) (Goal.atom (.bvar 0)))
      (Goal.imp
        (Goal.imp (encode ψ) (Goal.atom (.bvar 0)))
        (Goal.atom (.bvar 0)))
  let p := freshAtomForGoal P body
  have hp_not_mem : p ∉ atoms := freshAtomForGoal_not_in_atomicBase atoms body
  have hOr : SearchSupports P (encode φ) ∨ SearchSupports P (encode ψ) := by
    by_cases hφ : SearchSupports P (encode φ)
    · exact Or.inl hφ
    · by_cases hψ : SearchSupports P (encode ψ)
      · exact Or.inr hψ
      · have hp_mem : p ∈ atoms :=
          h atoms (fun a ha => ha) p
            (fun hφ' => False.elim (hφ hφ'))
            (fun hψ' => False.elim (hψ hψ'))
        exact False.elim (hp_not_mem hp_mem)
  rcases hOr with hφ | hψ
  · exact disj_search_of_left (atomicBase atoms) φ ψ hφ
  · exact disj_search_of_right (atomicBase atoms) φ ψ hψ

end Contextual
end HeytingLean.PTS.BaseExtension
