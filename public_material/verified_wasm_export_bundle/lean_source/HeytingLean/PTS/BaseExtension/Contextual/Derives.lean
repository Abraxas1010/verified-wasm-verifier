import HeytingLean.PTS.BaseExtension.Contextual.Context

namespace HeytingLean.PTS.BaseExtension.Contextual

/-!
# Existential-fresh derivation layer

`search` hard-codes `freshAtomForGoal` in the universal case. The proof-theoretic
lemmas needed to remove the remaining bridge axioms instead want a derivation
system where the universal rule may choose any atom that is fresh for the
current program and goal body.
-/

mutual
  inductive Derives : Program → Goal → Prop where
    | atom {P : Program} {a : AtomVar} :
        DerivesFromAny P P a →
        Derives P (.atom a)
    | imp {P : Program} {g₁ g₂ : Goal} :
        Derives (g₁ :: P) g₂ →
        Derives P (.imp g₁ g₂)
    | conj {P : Program} {g₁ g₂ : Goal} :
        Derives P g₁ →
        Derives P g₂ →
        Derives P (.conj g₁ g₂)
    | disjLeft {P : Program} {g₁ g₂ : Goal} :
        Derives P g₁ →
        Derives P (.disj g₁ g₂)
    | disjRight {P : Program} {g₁ g₂ : Goal} :
        Derives P g₂ →
        Derives P (.disj g₁ g₂)
    | all {P : Program} {g : Goal} (a : Atom) :
        a ∉ programAtoms P →
        a ∉ goalAtoms g →
        Derives P (substGoal g 0 a) →
        Derives P (.all g)

  inductive DerivesFromAny : Program → List Goal → AtomVar → Prop where
    | here {P : Program} {g : Goal} {rest : List Goal} {a : AtomVar} :
        Fires P g a →
        DerivesFromAny P (g :: rest) a
    | there {P : Program} {g : Goal} {rest : List Goal} {a : AtomVar} :
        DerivesFromAny P rest a →
        DerivesFromAny P (g :: rest) a

  inductive Fires : Program → Goal → AtomVar → Prop where
    | atom {P : Program} {a : AtomVar} :
        Fires P (.atom a) a
    | imp {P : Program} {g₁ g₂ : Goal} {a : AtomVar} :
        Derives P g₁ →
        Fires P g₂ a →
        Fires P (.imp g₁ g₂) a
    | allAtom {P : Program} {g : Goal} (atm : Atom) :
        Fires P (substGoal g 0 atm) (.atom atm) →
        Fires P (.all g) (.atom atm)
    | allBvar {P : Program} {g : Goal} {k : Nat} (a : Atom) :
        a ∉ programAtoms P →
        a ∉ goalAtoms g →
        Fires P (substGoal g 0 a) (.bvar k) →
        Fires P (.all g) (.bvar k)
end

private theorem le_maxAtomId_of_mem {atoms : List Atom} {a : Atom} (h : a ∈ atoms) :
    a.id ≤ maxAtomId atoms := by
  induction atoms with
  | nil =>
      cases h
  | cons hd tl ih =>
      simp [maxAtomId] at h ⊢
      rcases h with rfl | htl
      · exact Nat.le_max_left _ _
      · exact le_trans (ih htl) (Nat.le_max_right _ _)

private theorem freshAtomLiteral_not_mem (atoms : List Atom) :
    ({ id := maxAtomId atoms + 1 } : Atom) ∉ atoms := by
  intro hmem
  have hle :
      (({ id := maxAtomId atoms + 1 } : Atom)).id ≤ maxAtomId atoms :=
    le_maxAtomId_of_mem hmem
  exact Nat.not_succ_le_self _ (by simpa using hle)

theorem freshAtomForGoal_fresh (P : Program) (g : Goal) :
    freshAtomForGoal P g ∉ programAtoms P ∧ freshAtomForGoal P g ∉ goalAtoms g := by
  unfold freshAtomForGoal
  constructor
  · intro hmem
    exact freshAtomLiteral_not_mem (programAtoms P ++ goalAtoms g)
      (List.mem_append.mpr (Or.inl hmem))
  · intro hmem
    exact freshAtomLiteral_not_mem (programAtoms P ++ goalAtoms g)
      (List.mem_append.mpr (Or.inr hmem))

mutual
  def relabelAtomVar (ρ : Atom → Atom) : AtomVar → AtomVar
    | .atom a => .atom (ρ a)
    | .bvar k => .bvar k

  def relabelGoal (ρ : Atom → Atom) : Goal → Goal
    | .atom v => .atom (relabelAtomVar ρ v)
    | .imp g₁ g₂ => .imp (relabelGoal ρ g₁) (relabelGoal ρ g₂)
    | .conj g₁ g₂ => .conj (relabelGoal ρ g₁) (relabelGoal ρ g₂)
    | .disj g₁ g₂ => .disj (relabelGoal ρ g₁) (relabelGoal ρ g₂)
    | .all g => .all (relabelGoal ρ g)
end

def relabelProgram (ρ : Atom → Atom) (P : Program) : Program :=
  P.map (relabelGoal ρ)

def replaceAtom (c a : Atom) : Atom → Atom :=
  fun x => if x = c then a else x

theorem replaceAtom_fix_of_ne {c a x : Atom} (hx : x ≠ c) :
    replaceAtom c a x = x := by
  simp [replaceAtom, hx]

theorem relabelAtomVar_comp {ρ σ : Atom → Atom} {v : AtomVar} :
    relabelAtomVar σ (relabelAtomVar ρ v) = relabelAtomVar (σ ∘ ρ) v := by
  cases v <;> rfl

theorem relabelGoal_comp {ρ σ : Atom → Atom} {g : Goal} :
    relabelGoal σ (relabelGoal ρ g) = relabelGoal (σ ∘ ρ) g := by
  induction g with
  | atom v =>
      simpa [relabelGoal] using (relabelAtomVar_comp (ρ := ρ) (σ := σ) (v := v))
  | imp g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal, ih₁, ih₂]
  | conj g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal, ih₁, ih₂]
  | disj g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal, ih₁, ih₂]
  | all g ih =>
      simp [relabelGoal, ih]

theorem relabelProgram_comp {ρ σ : Atom → Atom} {P : Program} :
    relabelProgram σ (relabelProgram ρ P) = relabelProgram (σ ∘ ρ) P := by
  induction P with
  | nil =>
      rfl
  | cons g rest ih =>
      simp [relabelProgram, relabelGoal_comp]

theorem relabelAtomVar_substAtomVar_comm {ρ : Atom → Atom} {n : Nat} {atm : Atom}
    {v : AtomVar} :
    relabelAtomVar ρ (substAtomVar n atm v) =
      substAtomVar n (ρ atm) (relabelAtomVar ρ v) := by
  cases v with
  | atom a =>
      simp [relabelAtomVar, substAtomVar]
  | bvar k =>
      by_cases hk : k = n
      · simp [relabelAtomVar, substAtomVar, hk]
      · simp [relabelAtomVar, substAtomVar, hk]

theorem relabelGoal_substGoal_comm {ρ : Atom → Atom} {g : Goal} {n : Nat} {atm : Atom} :
    relabelGoal ρ (substGoal g n atm) =
      substGoal (relabelGoal ρ g) n (ρ atm) := by
  induction g generalizing n with
  | atom v =>
      simpa [relabelGoal, substGoal] using
        (relabelAtomVar_substAtomVar_comm (ρ := ρ) (n := n) (atm := atm) (v := v))
  | imp g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal, substGoal, ih₁, ih₂]
  | conj g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal, substGoal, ih₁, ih₂]
  | disj g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal, substGoal, ih₁, ih₂]
  | all g ih =>
      simp [relabelGoal, substGoal, ih]

theorem goalAtoms_relabelGoal {ρ : Atom → Atom} {g : Goal} :
    goalAtoms (relabelGoal ρ g) = (goalAtoms g).map ρ := by
  induction g with
  | atom v =>
      cases v with
      | atom a =>
          simp [relabelGoal, relabelAtomVar, goalAtoms, atomVarAtoms]
      | bvar k =>
          simp [relabelGoal, relabelAtomVar, goalAtoms, atomVarAtoms]
  | imp g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal, goalAtoms, ih₁, ih₂, List.map_append]
  | conj g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal, goalAtoms, ih₁, ih₂, List.map_append]
  | disj g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal, goalAtoms, ih₁, ih₂, List.map_append]
  | all g ih =>
      simp [relabelGoal, goalAtoms, ih]

theorem programAtoms_relabelProgram {ρ : Atom → Atom} {P : Program} :
    programAtoms (relabelProgram ρ P) = (programAtoms P).map ρ := by
  induction P with
  | nil =>
      simp [relabelProgram, programAtoms]
  | cons g rest ih =>
      have hmaps :
          List.map (goalAtoms ∘ relabelGoal ρ) rest =
            List.map (List.map ρ ∘ goalAtoms) rest := by
        ext x
        simp [Function.comp, goalAtoms_relabelGoal]
      simp [relabelProgram, programAtoms, goalAtoms_relabelGoal, List.map_append, hmaps]

theorem relabelGoal_fresh {ρ : Atom → Atom} (hρ : Function.Injective ρ)
    {a : Atom} {g : Goal} (ha : a ∉ goalAtoms g) :
    ρ a ∉ goalAtoms (relabelGoal ρ g) := by
  rw [goalAtoms_relabelGoal]
  intro hmem
  rcases List.mem_map.mp hmem with ⟨b, hb, hEq⟩
  apply ha
  have : b = a := hρ hEq
  simpa [this] using hb

theorem relabelProgram_fresh {ρ : Atom → Atom} (hρ : Function.Injective ρ)
    {a : Atom} {P : Program} (ha : a ∉ programAtoms P) :
    ρ a ∉ programAtoms (relabelProgram ρ P) := by
  rw [programAtoms_relabelProgram]
  intro hmem
  rcases List.mem_map.mp hmem with ⟨b, hb, hEq⟩
  apply ha
  have : b = a := hρ hEq
  simpa [this] using hb

theorem relabelGoal_id_of_fixed {ρ : Atom → Atom} {g : Goal}
    (hfix : ∀ a, a ∈ goalAtoms g → ρ a = a) :
    relabelGoal ρ g = g := by
  induction g with
  | atom v =>
      cases v with
      | atom a =>
          have ha : ρ a = a := hfix a (by simp [goalAtoms, atomVarAtoms])
          simp [relabelGoal, relabelAtomVar, ha]
      | bvar k =>
          simp [relabelGoal, relabelAtomVar]
  | imp g₁ g₂ ih₁ ih₂ =>
      have h₁ : ∀ a, a ∈ goalAtoms g₁ → ρ a = a := by
        intro a ha
        exact hfix a (by simp [goalAtoms, ha])
      have h₂ : ∀ a, a ∈ goalAtoms g₂ → ρ a = a := by
        intro a ha
        exact hfix a (by simp [goalAtoms, ha])
      simp [relabelGoal, ih₁ h₁, ih₂ h₂]
  | conj g₁ g₂ ih₁ ih₂ =>
      have h₁ : ∀ a, a ∈ goalAtoms g₁ → ρ a = a := by
        intro a ha
        exact hfix a (by simp [goalAtoms, ha])
      have h₂ : ∀ a, a ∈ goalAtoms g₂ → ρ a = a := by
        intro a ha
        exact hfix a (by simp [goalAtoms, ha])
      simp [relabelGoal, ih₁ h₁, ih₂ h₂]
  | disj g₁ g₂ ih₁ ih₂ =>
      have h₁ : ∀ a, a ∈ goalAtoms g₁ → ρ a = a := by
        intro a ha
        exact hfix a (by simp [goalAtoms, ha])
      have h₂ : ∀ a, a ∈ goalAtoms g₂ → ρ a = a := by
        intro a ha
        exact hfix a (by simp [goalAtoms, ha])
      simp [relabelGoal, ih₁ h₁, ih₂ h₂]
  | all g ih =>
      have h' : ∀ a, a ∈ goalAtoms g → ρ a = a := by
        intro a ha
        exact hfix a (by simpa [goalAtoms] using ha)
      simp [relabelGoal, ih h']

theorem relabelProgram_id_of_fixed {ρ : Atom → Atom} {P : Program}
    (hfix : ∀ a, a ∈ programAtoms P → ρ a = a) :
    relabelProgram ρ P = P := by
  induction P with
  | nil =>
      rfl
  | cons g rest ih =>
      have hg : ∀ a, a ∈ goalAtoms g → ρ a = a := by
        intro a ha
        exact hfix a (by simp [programAtoms, ha])
      have hrest : ∀ a, a ∈ programAtoms rest → ρ a = a := by
        intro a ha
        exact hfix a (by
          have : a ∈ goalAtoms g ++ programAtoms rest := List.mem_append.mpr (Or.inr ha)
          simpa [programAtoms] using this)
      simpa [relabelProgram, relabelGoal_id_of_fixed hg] using ih hrest

theorem relabelGoal_id_of_absent {g : Goal} {c a : Atom}
    (hc : c ∉ goalAtoms g) :
    relabelGoal (replaceAtom c a) g = g := by
  apply relabelGoal_id_of_fixed
  intro x hx
  exact replaceAtom_fix_of_ne (c := c) (a := a) (x := x) (by
    intro hEq
    exact hc (hEq ▸ hx))

theorem relabelProgram_id_of_absent {P : Program} {c a : Atom}
    (hc : c ∉ programAtoms P) :
    relabelProgram (replaceAtom c a) P = P := by
  apply relabelProgram_id_of_fixed
  intro x hx
  exact replaceAtom_fix_of_ne (c := c) (a := a) (x := x) (by
    intro hEq
    exact hc (hEq ▸ hx))

theorem relabelGoal_substGoal_zero_replace {g : Goal} {c a : Atom}
    (hc : c ∉ goalAtoms g) :
    relabelGoal (replaceAtom c a) (substGoal g 0 c) = substGoal g 0 a := by
  rw [relabelGoal_substGoal_comm]
  simp [relabelGoal_id_of_absent hc, replaceAtom]

mutual
  theorem derives_relabel {ρ : Atom → Atom} (hρ : Function.Injective ρ) :
      ∀ {P : Program} {g : Goal}, Derives P g → Derives (relabelProgram ρ P) (relabelGoal ρ g)
    | _, _, .atom h =>
        Derives.atom (derivesFromAny_relabel hρ h)
    | _, _, .imp h =>
        by
          simpa [relabelProgram, relabelGoal] using
            (Derives.imp (derives_relabel hρ h))
    | _, _, .conj h₁ h₂ =>
        Derives.conj (derives_relabel hρ h₁) (derives_relabel hρ h₂)
    | _, _, .disjLeft h =>
        Derives.disjLeft (derives_relabel hρ h)
    | _, _, .disjRight h =>
        Derives.disjRight (derives_relabel hρ h)
    | _, _, .all a haP hag hsub =>
        by
          refine Derives.all (ρ a) ?_ ?_ ?_
          · exact relabelProgram_fresh hρ haP
          · exact relabelGoal_fresh hρ hag
          · simpa [relabelGoal_substGoal_comm] using derives_relabel hρ hsub

  theorem derivesFromAny_relabel {ρ : Atom → Atom} (hρ : Function.Injective ρ) :
      ∀ {P : Program} {gs : List Goal} {a : AtomVar},
        DerivesFromAny P gs a →
          DerivesFromAny (relabelProgram ρ P) (List.map (relabelGoal ρ) gs) (relabelAtomVar ρ a)
    | _, _, _, .here h =>
        by
          simp
          exact DerivesFromAny.here (fires_relabel hρ h)
    | _, _, _, .there h =>
        by
          simp
          exact DerivesFromAny.there (derivesFromAny_relabel hρ h)

  theorem fires_relabel {ρ : Atom → Atom} (hρ : Function.Injective ρ) :
      ∀ {P : Program} {g : Goal} {a : AtomVar},
        Fires P g a → Fires (relabelProgram ρ P) (relabelGoal ρ g) (relabelAtomVar ρ a)
    | P, _, a, .atom =>
        by
          simpa [relabelGoal, relabelAtomVar] using
            (Fires.atom (P := relabelProgram ρ P) (a := relabelAtomVar ρ a))
    | _, _, _, .imp h₁ h₂ =>
        Fires.imp (derives_relabel hρ h₁) (fires_relabel hρ h₂)
    | P, .all g, _, .allAtom atm h =>
        by
          have h' :
              Fires (relabelProgram ρ P) (substGoal (relabelGoal ρ g) 0 (ρ atm)) (.atom (ρ atm)) := by
            simpa [relabelAtomVar, relabelGoal_substGoal_comm] using fires_relabel hρ h
          exact Fires.allAtom (ρ atm) h'
    | P, .all g, _, .allBvar atm freshP freshG h =>
        by
          refine Fires.allBvar (a := ρ atm) ?_ ?_ ?_
          · exact relabelProgram_fresh hρ freshP
          · exact relabelGoal_fresh hρ freshG
          · simpa [relabelGoal_substGoal_comm, relabelAtomVar] using
              (fires_relabel hρ h)
end

def swapAtoms (a b : Atom) : Atom → Atom :=
  fun x => if x = a then b else if x = b then a else x

theorem swapAtoms_involutive (a b : Atom) : Function.Involutive (swapAtoms a b) := by
  intro x
  by_cases hxa : x = a
  · subst hxa
    simp [swapAtoms]
  · by_cases hxb : x = b
    · simp [swapAtoms, hxb]
    · simp [swapAtoms, hxa, hxb]

theorem swapAtoms_injective (a b : Atom) : Function.Injective (swapAtoms a b) := by
  exact (swapAtoms_involutive a b).injective

theorem swapAtoms_self_left (a b : Atom) : swapAtoms a b a = b := by
  simp [swapAtoms]

theorem swapAtoms_self_right (a b : Atom) : swapAtoms a b b = a := by
  by_cases hab : b = a
  · simp [swapAtoms, hab]
  · simp [swapAtoms, hab]

theorem swapAtoms_fix_of_ne {a b x : Atom} (hxa : x ≠ a) (hxb : x ≠ b) :
    swapAtoms a b x = x := by
  simp [swapAtoms, hxa, hxb]

theorem swapAtoms_goal_id_of_fresh {a b : Atom} {g : Goal}
    (ha : a ∉ goalAtoms g) (hb : b ∉ goalAtoms g) :
    relabelGoal (swapAtoms a b) g = g := by
  apply relabelGoal_id_of_fixed
  intro x hx
  exact swapAtoms_fix_of_ne (by
    intro hEq
    exact ha (hEq ▸ hx)) (by
    intro hEq
    exact hb (hEq ▸ hx))

theorem swapAtoms_program_id_of_fresh {a b : Atom} {P : Program}
    (ha : a ∉ programAtoms P) (hb : b ∉ programAtoms P) :
    relabelProgram (swapAtoms a b) P = P := by
  apply relabelProgram_id_of_fixed
  intro x hx
  exact swapAtoms_fix_of_ne (by
    intro hEq
    exact ha (hEq ▸ hx)) (by
    intro hEq
    exact hb (hEq ▸ hx))

mutual
  private theorem search_equivariant_step (fuel : Nat) :
      (∀ (P : Program) (g : Goal) (ρ : Atom → Atom), Function.Injective ρ →
        search fuel (relabelProgram ρ P) (relabelGoal ρ g) = search fuel P g) ∧
      (∀ (P : Program) (gs : List Goal) (a : AtomVar) (ρ : Atom → Atom), Function.Injective ρ →
        searchAnyAssumption fuel (relabelProgram ρ P) (List.map (relabelGoal ρ) gs)
          (relabelAtomVar ρ a) = searchAnyAssumption fuel P gs a) ∧
      (∀ (P : Program) (g : Goal) (a : AtomVar) (ρ : Atom → Atom), Function.Injective ρ →
        fires fuel (relabelProgram ρ P) (relabelGoal ρ g) (relabelAtomVar ρ a) = fires fuel P g a) := by
    induction fuel with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · intro P g ρ hρ
          simp [search]
        · intro P gs a ρ hρ
          induction gs with
          | nil =>
              simp [searchAnyAssumption]
          | cons g rest ih =>
              simp [searchAnyAssumption, fires, ih]
        · intro P g a ρ hρ
          simp [fires]
    | succ fuel ih =>
        obtain ⟨ihSearch, ihAny, ihFires⟩ := ih
        have hFires : ∀ (P : Program) (g : Goal) (a : AtomVar) (ρ : Atom → Atom),
            Function.Injective ρ →
            fires (fuel + 1) (relabelProgram ρ P) (relabelGoal ρ g) (relabelAtomVar ρ a) =
              fires (fuel + 1) P g a := by
          intro P g a ρ hρ
          cases g with
          | atom b =>
              cases a <;> cases b <;> simp [fires, relabelGoal, relabelAtomVar, hρ.eq_iff]
          | imp g₁ g₂ =>
              simp [fires, relabelGoal, ihSearch P g₁ ρ hρ, ihFires P g₂ a ρ hρ]
          | conj g₁ g₂ =>
              simp [fires, relabelGoal]
          | disj g₁ g₂ =>
              simp [fires, relabelGoal]
          | all g =>
              cases a with
              | atom atm =>
                  simpa [fires, relabelGoal, relabelAtomVar, relabelGoal_substGoal_comm] using
                    ihFires P (substGoal g 0 atm) (.atom atm) ρ hρ
              | bvar k =>
                  let P' := relabelProgram ρ P
                  let g' := relabelGoal ρ g
                  let c := freshAtomForGoal P g
                  let c' := freshAtomForGoal P' g'
                  let τ : Atom → Atom := swapAtoms (ρ c) c'
                  have hρcP : ρ c ∉ programAtoms P' :=
                    relabelProgram_fresh hρ (freshAtomForGoal_fresh P g).1
                  have hρcg : ρ c ∉ goalAtoms g' :=
                    relabelGoal_fresh hρ (freshAtomForGoal_fresh P g).2
                  have hc'P : c' ∉ programAtoms P' := (freshAtomForGoal_fresh P' g').1
                  have hc'g : c' ∉ goalAtoms g' := (freshAtomForGoal_fresh P' g').2
                  have hτP : relabelProgram τ P' = P' :=
                    swapAtoms_program_id_of_fresh hρcP hc'P
                  have hτg : relabelGoal τ g' = g' :=
                    swapAtoms_goal_id_of_fresh hρcg hc'g
                  have hFirst :
                      fires fuel P' (substGoal g' 0 (ρ c)) (.bvar k) =
                        fires fuel P (substGoal g 0 c) (.bvar k) := by
                    simpa [P', g', c, relabelGoal_substGoal_comm, relabelAtomVar] using
                      ihFires P (substGoal g 0 c) (.bvar k) ρ hρ
                  have hSecond :
                      fires fuel P' (substGoal g' 0 c') (.bvar k) =
                        fires fuel P' (substGoal g' 0 (ρ c)) (.bvar k) := by
                    simpa [P', g', c, c', τ, hτP, hτg, relabelGoal_substGoal_comm, relabelAtomVar, swapAtoms] using
                      ihFires P' (substGoal g' 0 (ρ c)) (.bvar k) τ
                        (swapAtoms_injective (ρ c) c')
                  calc
                    fires (fuel + 1) P' (.all g') (.bvar k)
                        = fires fuel P' (substGoal g' 0 c') (.bvar k) := by
                            simp [fires, P', g', c']
                    _ = fires fuel P' (substGoal g' 0 (ρ c)) (.bvar k) := hSecond
                    _ = fires fuel P (substGoal g 0 c) (.bvar k) := hFirst
                    _ = fires (fuel + 1) P (.all g) (.bvar k) := by
                          simp [fires, c]
        have hAny : ∀ (P : Program) (gs : List Goal) (a : AtomVar) (ρ : Atom → Atom),
            Function.Injective ρ →
            searchAnyAssumption (fuel + 1) (relabelProgram ρ P) (List.map (relabelGoal ρ) gs)
              (relabelAtomVar ρ a) = searchAnyAssumption (fuel + 1) P gs a := by
          intro P gs a ρ hρ
          induction gs with
          | nil =>
              simp [searchAnyAssumption]
          | cons g rest ihGs =>
              simp [searchAnyAssumption, hFires P g a ρ hρ, ihGs]
        have hSearch : ∀ (P : Program) (g : Goal) (ρ : Atom → Atom),
            Function.Injective ρ →
            search (fuel + 1) (relabelProgram ρ P) (relabelGoal ρ g) = search (fuel + 1) P g := by
          intro P g ρ hρ
          cases g with
          | atom a =>
              simpa [search, relabelGoal, relabelProgram] using ihAny P P a ρ hρ
          | imp g₁ g₂ =>
              simpa [search, relabelGoal, relabelProgram] using ihSearch (g₁ :: P) g₂ ρ hρ
          | conj g₁ g₂ =>
              simp [search, relabelGoal, ihSearch P g₁ ρ hρ, ihSearch P g₂ ρ hρ]
          | disj g₁ g₂ =>
              simp [search, relabelGoal, ihSearch P g₁ ρ hρ, ihSearch P g₂ ρ hρ]
          | all g =>
              let P' := relabelProgram ρ P
              let g' := relabelGoal ρ g
              let c := freshAtomForGoal P g
              let c' := freshAtomForGoal P' g'
              let τ : Atom → Atom := swapAtoms (ρ c) c'
              have hρcP : ρ c ∉ programAtoms P' :=
                relabelProgram_fresh hρ (freshAtomForGoal_fresh P g).1
              have hρcg : ρ c ∉ goalAtoms g' :=
                relabelGoal_fresh hρ (freshAtomForGoal_fresh P g).2
              have hc'P : c' ∉ programAtoms P' := (freshAtomForGoal_fresh P' g').1
              have hc'g : c' ∉ goalAtoms g' := (freshAtomForGoal_fresh P' g').2
              have hτP : relabelProgram τ P' = P' :=
                swapAtoms_program_id_of_fresh hρcP hc'P
              have hτg : relabelGoal τ g' = g' :=
                swapAtoms_goal_id_of_fresh hρcg hc'g
              have hFirst :
                  search fuel P' (substGoal g' 0 (ρ c)) =
                    search fuel P (substGoal g 0 c) := by
                simpa [P', g', c, relabelGoal_substGoal_comm] using
                  ihSearch P (substGoal g 0 c) ρ hρ
              have hSecond :
                  search fuel P' (substGoal g' 0 c') =
                    search fuel P' (substGoal g' 0 (ρ c)) := by
                simpa [P', g', c, c', τ, hτP, hτg, relabelGoal_substGoal_comm, swapAtoms] using
                  ihSearch P' (substGoal g' 0 (ρ c)) τ (swapAtoms_injective (ρ c) c')
              calc
                search (fuel + 1) P' (.all g')
                    = search fuel P' (substGoal g' 0 c') := by
                        simp [search, P', g', c']
                _ = search fuel P' (substGoal g' 0 (ρ c)) := hSecond
                _ = search fuel P (substGoal g 0 c) := hFirst
                _ = search (fuel + 1) P (.all g) := by
                      simp [search, c]
        exact ⟨hSearch, hAny, hFires⟩
end

theorem search_equivariant (fuel : Nat) (P : Program) (g : Goal) (ρ : Atom → Atom)
    (hρ : Function.Injective ρ) :
    search fuel (relabelProgram ρ P) (relabelGoal ρ g) = search fuel P g :=
  (search_equivariant_step fuel).1 P g ρ hρ

theorem searchAnyAssumption_equivariant (fuel : Nat) (P : Program) (gs : List Goal)
    (a : AtomVar) (ρ : Atom → Atom) (hρ : Function.Injective ρ) :
    searchAnyAssumption fuel (relabelProgram ρ P) (List.map (relabelGoal ρ) gs)
      (relabelAtomVar ρ a) = searchAnyAssumption fuel P gs a :=
  (search_equivariant_step fuel).2.1 P gs a ρ hρ

theorem fires_equivariant (fuel : Nat) (P : Program) (g : Goal) (a : AtomVar)
    (ρ : Atom → Atom) (hρ : Function.Injective ρ) :
    fires fuel (relabelProgram ρ P) (relabelGoal ρ g) (relabelAtomVar ρ a) = fires fuel P g a :=
  (search_equivariant_step fuel).2.2 P g a ρ hρ

private theorem searchAnyAssumption_of_mem_fires {fuel : Nat} {P : Program} {gs : List Goal}
    {g : Goal} {a : AtomVar} (hg : g ∈ gs) (hf : fires fuel P g a = true) :
    searchAnyAssumption fuel P gs a = true := by
  induction gs with
  | nil =>
      cases hg
  | cons g' rest ih =>
      simp at hg
      simp [searchAnyAssumption]
      rcases hg with rfl | hg
      · exact Or.inl hf
      · exact Or.inr (ih hg)

private theorem mem_programAtoms_of_mem_goal {P : Program} {g : Goal} {a : Atom}
    (hg : g ∈ P) (ha : a ∈ goalAtoms g) :
    a ∈ programAtoms P := by
  induction P with
  | nil =>
      cases hg
  | cons head tail ih =>
      simp at hg
      rcases hg with rfl | hg
      · have : a ∈ goalAtoms g ++ programAtoms tail := List.mem_append.mpr (Or.inl ha)
        simpa [programAtoms] using this
      · have htail : a ∈ programAtoms tail := ih hg
        have : a ∈ goalAtoms head ++ programAtoms tail := List.mem_append.mpr (Or.inr htail)
        simpa [programAtoms] using this

private theorem programAtoms_mono_of_program_mono {P P' : Program}
    (hPP' : ∀ x, x ∈ P → x ∈ P') :
    ∀ a, a ∈ programAtoms P → a ∈ programAtoms P' := by
  intro a ha
  induction P generalizing P' with
  | nil =>
      cases ha
  | cons g rest ih =>
      have hsplit : a ∈ goalAtoms g ++ programAtoms rest := by
        simpa [programAtoms] using ha
      rcases List.mem_append.mp hsplit with hga | hrest
      · exact mem_programAtoms_of_mem_goal (hPP' g (by simp)) hga
      · have hPP'rest : ∀ x, x ∈ rest → x ∈ P' := by
          intro x hx
          exact hPP' x (by simp [hx])
        exact ih hPP'rest hrest

mutual
  private theorem search_mono_program_step (fuel : Nat) :
      (∀ (P P' : Program) (g : Goal), (∀ x, x ∈ P → x ∈ P') →
        search fuel P g = true → search fuel P' g = true) ∧
      (∀ (P P' : Program) (gs gs' : List Goal) (a : AtomVar),
        (∀ x, x ∈ P → x ∈ P') →
        (∀ x, x ∈ gs → x ∈ gs') →
        searchAnyAssumption fuel P gs a = true →
        searchAnyAssumption fuel P' gs' a = true) ∧
      (∀ (P P' : Program) (g : Goal) (a : AtomVar), (∀ x, x ∈ P → x ∈ P') →
        fires fuel P g a = true → fires fuel P' g a = true) := by
    induction fuel with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · intro P P' g hPP' h
          simp [search] at h
        · intro P P' gs gs' a hPP' hgs h
          induction gs with
          | nil =>
              simp [searchAnyAssumption] at h
          | cons g rest ih =>
              simp [searchAnyAssumption, fires] at h
              exact ih (by
                intro x hx
                exact hgs x (by simp [hx])) h
        · intro P P' g a hPP' h
          simp [fires] at h
    | succ fuel ih =>
        obtain ⟨ihSearch, ihAny, ihFires⟩ := ih
        have hFires : ∀ (P P' : Program) (g : Goal) (a : AtomVar), (∀ x, x ∈ P → x ∈ P') →
            fires (fuel + 1) P g a = true → fires (fuel + 1) P' g a = true := by
          intro P P' g a hPP' h
          cases g with
          | atom b =>
              simpa [fires] using h
          | imp g₁ g₂ =>
              simp [fires, Bool.and_eq_true] at h ⊢
              exact ⟨ihSearch P P' g₁ hPP' h.1, ihFires P P' g₂ a hPP' h.2⟩
          | conj g₁ g₂ =>
              simp [fires] at h
          | disj g₁ g₂ =>
              simp [fires] at h
          | all g =>
              cases a with
              | atom atm =>
                  have h' : fires fuel P (substGoal g 0 atm) (.atom atm) = true := by
                    simpa [fires] using h
                  simpa [fires] using ihFires P P' (substGoal g 0 atm) (.atom atm) hPP' h'
              | bvar k =>
                  let c := freshAtomForGoal P g
                  let c' := freshAtomForGoal P' g
                  let τ : Atom → Atom := swapAtoms c c'
                  have hcP : c ∉ programAtoms P := (freshAtomForGoal_fresh P g).1
                  have hcg : c ∉ goalAtoms g := (freshAtomForGoal_fresh P g).2
                  have hc'P' : c' ∉ programAtoms P' := (freshAtomForGoal_fresh P' g).1
                  have hc'g : c' ∉ goalAtoms g := (freshAtomForGoal_fresh P' g).2
                  have hc'P : c' ∉ programAtoms P := by
                    intro hc'Pmem
                    exact hc'P' (programAtoms_mono_of_program_mono hPP' c' hc'Pmem)
                  have hτP : relabelProgram τ P = P :=
                    swapAtoms_program_id_of_fresh hcP hc'P
                  have hτg : relabelGoal τ g = g :=
                    swapAtoms_goal_id_of_fresh hcg hc'g
                  have hsub : fires fuel P (substGoal g 0 c) (.bvar k) = true := by
                    simpa [fires, c] using h
                  have hRenameEq :
                      fires fuel P (substGoal g 0 c') (.bvar k) =
                        fires fuel P (substGoal g 0 c) (.bvar k) := by
                    simpa [τ, c, c', hτP, hτg, relabelGoal_substGoal_comm, relabelAtomVar, swapAtoms] using
                      fires_equivariant fuel P (substGoal g 0 c) (.bvar k) τ
                        (swapAtoms_injective c c')
                  have hRename : fires fuel P (substGoal g 0 c') (.bvar k) = true := by
                    rw [hRenameEq]
                    exact hsub
                  have hMonoSub : fires fuel P' (substGoal g 0 c') (.bvar k) = true :=
                    ihFires P P' (substGoal g 0 c') (.bvar k) hPP' hRename
                  simpa [fires, c'] using hMonoSub
        have hAny : ∀ (P P' : Program) (gs gs' : List Goal) (a : AtomVar),
            (∀ x, x ∈ P → x ∈ P') →
            (∀ x, x ∈ gs → x ∈ gs') →
            searchAnyAssumption (fuel + 1) P gs a = true →
            searchAnyAssumption (fuel + 1) P' gs' a = true := by
          intro P P' gs gs' a hPP' hgs h
          induction gs generalizing gs' with
          | nil =>
              simp [searchAnyAssumption] at h
          | cons g rest ihGs =>
              simp [searchAnyAssumption, Bool.or_eq_true] at h
              rcases h with h | h
              · exact searchAnyAssumption_of_mem_fires
                  (hgs g (by simp)) (hFires P P' g a hPP' h)
              · exact ihGs gs'
                  (by
                    intro x hx
                    exact hgs x (by simp [hx]))
                  h
        have hSearch : ∀ (P P' : Program) (g : Goal), (∀ x, x ∈ P → x ∈ P') →
            search (fuel + 1) P g = true → search (fuel + 1) P' g = true := by
          intro P P' g hPP' h
          cases g with
          | atom a =>
              have h' : searchAnyAssumption fuel P P a = true := by
                simpa [search] using h
              simpa [search] using ihAny P P' P P' a hPP' hPP' h'
          | imp g₁ g₂ =>
              have hPP'' : ∀ x, x ∈ g₁ :: P → x ∈ g₁ :: P' := by
                intro x hx
                simp at hx ⊢
                rcases hx with rfl | hx
                · exact Or.inl rfl
                · exact Or.inr (hPP' x hx)
              have h' : search fuel (g₁ :: P) g₂ = true := by
                simpa [search] using h
              simpa [search] using ihSearch (g₁ :: P) (g₁ :: P') g₂ hPP'' h'
          | conj g₁ g₂ =>
              simp [search, Bool.and_eq_true] at h ⊢
              exact ⟨ihSearch P P' g₁ hPP' h.1, ihSearch P P' g₂ hPP' h.2⟩
          | disj g₁ g₂ =>
              simp [search, Bool.or_eq_true] at h ⊢
              rcases h with h | h
              · exact Or.inl (ihSearch P P' g₁ hPP' h)
              · exact Or.inr (ihSearch P P' g₂ hPP' h)
          | all g =>
              let c := freshAtomForGoal P g
              let c' := freshAtomForGoal P' g
              let τ : Atom → Atom := swapAtoms c c'
              have hcP : c ∉ programAtoms P := (freshAtomForGoal_fresh P g).1
              have hcg : c ∉ goalAtoms g := (freshAtomForGoal_fresh P g).2
              have hc'P' : c' ∉ programAtoms P' := (freshAtomForGoal_fresh P' g).1
              have hc'g : c' ∉ goalAtoms g := (freshAtomForGoal_fresh P' g).2
              have hc'P : c' ∉ programAtoms P := by
                intro hc'Pmem
                exact hc'P' (programAtoms_mono_of_program_mono hPP' c' hc'Pmem)
              have hτP : relabelProgram τ P = P :=
                swapAtoms_program_id_of_fresh hcP hc'P
              have hτg : relabelGoal τ g = g :=
                swapAtoms_goal_id_of_fresh hcg hc'g
              have hsub : search fuel P (substGoal g 0 c) = true := by
                simpa [search, c] using h
              have hRenameEq :
                  search fuel P (substGoal g 0 c') =
                    search fuel P (substGoal g 0 c) := by
                simpa [τ, c, c', hτP, hτg, relabelGoal_substGoal_comm, swapAtoms] using
                  search_equivariant fuel P (substGoal g 0 c) τ (swapAtoms_injective c c')
              have hRename : search fuel P (substGoal g 0 c') = true := by
                rw [hRenameEq]
                exact hsub
              have hMonoSub : search fuel P' (substGoal g 0 c') = true :=
                ihSearch P P' (substGoal g 0 c') hPP' hRename
              simpa [search, c'] using hMonoSub
        exact ⟨hSearch, hAny, hFires⟩
end

theorem search_mono_program (fuel : Nat) (P P' : Program) (g : Goal) :
    (∀ x, x ∈ P → x ∈ P') → search fuel P g = true → search fuel P' g = true :=
  (search_mono_program_step fuel).1 P P' g

theorem search_weaken (fuel : Nat) (P : Program) (extras : List Goal) (g : Goal) :
    search fuel P g = true → search fuel (extras ++ P) g = true := by
  apply search_mono_program fuel P (extras ++ P) g
  intro x hx
  exact List.mem_append.mpr (Or.inr hx)

private theorem fuel_step_mono (fuel : Nat) :
    (∀ P g, search fuel P g = true → search (fuel + 1) P g = true) ∧
    (∀ P gs a, searchAnyAssumption fuel P gs a = true →
      searchAnyAssumption (fuel + 1) P gs a = true) ∧
    (∀ P g a, fires fuel P g a = true → fires (fuel + 1) P g a = true) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro P g h
        simp [search] at h
      · intro P gs a h
        have hf0 : ∀ gs', searchAnyAssumption 0 P gs' a = false := by
          intro gs'
          induction gs' with
          | nil =>
              simp [searchAnyAssumption]
          | cons g rest ih =>
              simp [searchAnyAssumption, fires, ih]
        rw [hf0] at h
        exact absurd h (by decide)
      · intro P g a h
        simp [fires] at h
  | succ fuel ih =>
      obtain ⟨ihSearch, ihAny, ihFires⟩ := ih
      have hFires : ∀ P g a, fires (fuel + 1) P g a = true → fires (fuel + 1 + 1) P g a = true := by
        intro P g a h
        cases g with
        | atom b =>
            simpa [fires] using h
        | imp g₁ g₂ =>
            simp [fires, Bool.and_eq_true] at h ⊢
            exact ⟨ihSearch P g₁ h.1, ihFires P g₂ a h.2⟩
        | conj g₁ g₂ =>
            simp [fires] at h
        | disj g₁ g₂ =>
            simp [fires] at h
        | all g =>
            cases a with
            | atom atm =>
                simp only [fires] at h ⊢
                exact ihFires P _ _ h
            | bvar k =>
                simp only [fires] at h ⊢
                exact ihFires P _ _ h
      have hAny : ∀ P gs a, searchAnyAssumption (fuel + 1) P gs a = true →
          searchAnyAssumption (fuel + 1 + 1) P gs a = true := by
        intro P gs a h
        induction gs with
        | nil =>
            simp [searchAnyAssumption] at h
        | cons g rest ihGs =>
            simp [searchAnyAssumption, Bool.or_eq_true] at h ⊢
            rcases h with h | h
            · exact Or.inl (hFires P g a h)
            · exact Or.inr (ihGs h)
      have hSearch : ∀ P g, search (fuel + 1) P g = true → search (fuel + 1 + 1) P g = true := by
        intro P g h
        cases g with
        | atom a =>
            simp only [search] at h ⊢
            exact ihAny P P a h
        | imp g₁ g₂ =>
            simp only [search] at h ⊢
            exact ihSearch (g₁ :: P) g₂ h
        | conj g₁ g₂ =>
            simp [search, Bool.and_eq_true] at h ⊢
            exact ⟨ihSearch P g₁ h.1, ihSearch P g₂ h.2⟩
        | disj g₁ g₂ =>
            simp [search, Bool.or_eq_true] at h ⊢
            rcases h with h | h
            · exact Or.inl (ihSearch P g₁ h)
            · exact Or.inr (ihSearch P g₂ h)
        | all g =>
            simp only [search] at h ⊢
            exact ihSearch P _ h
      exact ⟨hSearch, hAny, hFires⟩

theorem search_fuel_mono (fuel extra : Nat) (P : Program) (g : Goal) :
    search fuel P g = true → search (fuel + extra) P g = true := by
  induction extra with
  | zero =>
      simp
  | succ extra ih =>
      intro h
      have h' := ih h
      rw [Nat.add_succ]
      exact (fuel_step_mono (fuel + extra)).1 P g h'

theorem fires_fuel_mono (fuel extra : Nat) (P : Program) (g : Goal) (a : AtomVar) :
    fires fuel P g a = true → fires (fuel + extra) P g a = true := by
  induction extra with
  | zero =>
      simp
  | succ extra ih =>
      intro h
      have h' := ih h
      rw [Nat.add_succ]
      exact (fuel_step_mono (fuel + extra)).2.2 P g a h'

private theorem search_to_derives_step (fuel : Nat) :
    (∀ P g, search fuel P g = true → Derives P g) ∧
    (∀ P gs a, searchAnyAssumption fuel P gs a = true → DerivesFromAny P gs a) ∧
    (∀ P g a, fires fuel P g a = true → Fires P g a) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro P g h
        simp [search] at h
      · intro P gs a h
        induction gs with
        | nil =>
            simp [searchAnyAssumption] at h
        | cons g rest ih =>
            simp [searchAnyAssumption, fires] at h
            exact DerivesFromAny.there (ih h)
      · intro P g a h
        simp [fires] at h
  | succ fuel ih =>
      obtain ⟨ihSearch, ihAny, ihFires⟩ := ih
      have hFires : ∀ P g a, fires (fuel + 1) P g a = true → Fires P g a := by
        intro P g a h
        cases g with
        | atom b =>
            simp [fires] at h
            have hb : b = a := by
              simpa using h
            subst hb
            exact Fires.atom
        | imp g₁ g₂ =>
            simp [fires, Bool.and_eq_true] at h
            exact Fires.imp (ihSearch P g₁ h.1) (ihFires P g₂ a h.2)
        | conj g₁ g₂ =>
            simp [fires] at h
        | disj g₁ g₂ =>
            simp [fires] at h
        | all g =>
            cases a with
            | atom atm =>
                simp [fires] at h
                exact Fires.allAtom atm (ihFires P (substGoal g 0 atm) (.atom atm) h)
            | bvar k =>
                simp [fires] at h
                exact Fires.allBvar (a := freshAtomForGoal P g)
                  (freshAtomForGoal_fresh P g).1
                  (freshAtomForGoal_fresh P g).2
                  (ihFires P (substGoal g 0 (freshAtomForGoal P g)) (.bvar k) h)
      have hAny : ∀ P gs a, searchAnyAssumption (fuel + 1) P gs a = true → DerivesFromAny P gs a := by
        intro P gs a h
        induction gs with
        | nil =>
            simp [searchAnyAssumption] at h
        | cons g rest ihGs =>
            simp [searchAnyAssumption, Bool.or_eq_true] at h
            rcases h with h | h
            · exact DerivesFromAny.here (hFires P g a h)
            · exact DerivesFromAny.there (ihGs h)
      have hSearch : ∀ P g, search (fuel + 1) P g = true → Derives P g := by
        intro P g h
        cases g with
        | atom a =>
            simp [search] at h
            exact Derives.atom (ihAny P P a h)
        | imp g₁ g₂ =>
            simp [search] at h
            exact Derives.imp (ihSearch (g₁ :: P) g₂ h)
        | conj g₁ g₂ =>
            simp [search, Bool.and_eq_true] at h
            exact Derives.conj (ihSearch P g₁ h.1) (ihSearch P g₂ h.2)
        | disj g₁ g₂ =>
            simp [search, Bool.or_eq_true] at h
            rcases h with h | h
            · exact Derives.disjLeft (ihSearch P g₁ h)
            · exact Derives.disjRight (ihSearch P g₂ h)
        | all g =>
            simp [search] at h
            exact Derives.all (freshAtomForGoal P g)
              (freshAtomForGoal_fresh P g).1
              (freshAtomForGoal_fresh P g).2
              (ihSearch P (substGoal g 0 (freshAtomForGoal P g)) h)
      exact ⟨hSearch, hAny, hFires⟩

theorem search_to_derives {fuel : Nat} {P : Program} {g : Goal} :
    search fuel P g = true → Derives P g :=
  (search_to_derives_step fuel).1 P g

theorem searchAnyAssumption_to_derives {fuel : Nat} {P : Program} {gs : List Goal} {a : AtomVar} :
    searchAnyAssumption fuel P gs a = true → DerivesFromAny P gs a :=
  (search_to_derives_step fuel).2.1 P gs a

theorem fires_to_derives {fuel : Nat} {P : Program} {g : Goal} {a : AtomVar} :
    fires fuel P g a = true → Fires P g a :=
  (search_to_derives_step fuel).2.2 P g a

mutual
  private theorem derives_to_search_relabel :
      ∀ {P : Program} {g : Goal}, Derives P g →
        ∀ {ρ : Atom → Atom}, Function.Injective ρ →
          SearchSupports (relabelProgram ρ P) (relabelGoal ρ g)
    | P, .atom a, .atom h, ρ, hρ =>
        by
          obtain ⟨fuel, hfuel⟩ := derivesFromAny_to_search_relabel h hρ
          exact ⟨fuel + 1, by simpa [search, relabelProgram, relabelGoal] using hfuel⟩
    | P, .imp g₁ g₂, .imp h, ρ, hρ =>
        by
          obtain ⟨fuel, hfuel⟩ := derives_to_search_relabel h hρ
          exact ⟨fuel + 1, by simpa [search, relabelProgram, relabelGoal] using hfuel⟩
    | P, .conj g₁ g₂, .conj h₁ h₂, ρ, hρ =>
        by
          obtain ⟨fuel₁, h₁fuel⟩ := derives_to_search_relabel h₁ hρ
          obtain ⟨fuel₂, h₂fuel⟩ := derives_to_search_relabel h₂ hρ
          let P' := relabelProgram ρ P
          let g₁' := relabelGoal ρ g₁
          let g₂' := relabelGoal ρ g₂
          have h₁mono : search (fuel₁ + fuel₂) P' g₁' = true :=
            search_fuel_mono fuel₁ fuel₂ P' g₁' h₁fuel
          have h₂mono : search (fuel₁ + fuel₂) P' g₂' = true := by
            simpa [Nat.add_comm] using search_fuel_mono fuel₂ fuel₁ P' g₂' h₂fuel
          exact ⟨fuel₁ + fuel₂ + 1, by
            simpa [search, relabelGoal, P', g₁', g₂', Bool.and_eq_true] using And.intro h₁mono h₂mono⟩
    | P, .disj g₁ g₂, .disjLeft h, ρ, hρ =>
        by
          obtain ⟨fuel, hfuel⟩ := derives_to_search_relabel h hρ
          refine ⟨fuel + 1, ?_⟩
          simp [search, relabelGoal, hfuel]
    | P, .disj g₁ g₂, .disjRight h, ρ, hρ =>
        by
          obtain ⟨fuel, hfuel⟩ := derives_to_search_relabel h hρ
          refine ⟨fuel + 1, ?_⟩
          simp [search, relabelGoal, hfuel]
    | P, .all g, .all a haP hag hsub, ρ, hρ =>
        by
          let P' := relabelProgram ρ P
          let g' := relabelGoal ρ g
          let a' := ρ a
          let c := freshAtomForGoal P' g'
          let τ : Atom → Atom := swapAtoms a' c
          let σ : Atom → Atom := τ ∘ ρ
          have hσ : Function.Injective σ := (swapAtoms_injective a' c).comp hρ
          have ha'P : a' ∉ programAtoms P' := relabelProgram_fresh hρ haP
          have ha'g : a' ∉ goalAtoms g' := relabelGoal_fresh hρ hag
          have hcP : c ∉ programAtoms P' := (freshAtomForGoal_fresh P' g').1
          have hcg : c ∉ goalAtoms g' := (freshAtomForGoal_fresh P' g').2
          have hτP : relabelProgram τ P' = P' := swapAtoms_program_id_of_fresh ha'P hcP
          have hτg : relabelGoal τ g' = g' := swapAtoms_goal_id_of_fresh ha'g hcg
          obtain ⟨fuel, hfuel⟩ := derives_to_search_relabel hsub hσ
          have hPσ : relabelProgram σ P = P' := by
            rw [show σ = τ ∘ ρ by rfl]
            rw [← relabelProgram_comp (ρ := ρ) (σ := τ) (P := P)]
            simpa [P'] using hτP
          have hgσ :
              relabelGoal σ (substGoal g 0 a) = substGoal g' 0 c := by
            rw [show σ = τ ∘ ρ by rfl]
            rw [← relabelGoal_comp (ρ := ρ) (σ := τ) (g := substGoal g 0 a)]
            calc
              relabelGoal τ (relabelGoal ρ (substGoal g 0 a))
                  = relabelGoal τ (substGoal g' 0 a') := by
                      simp [g', a', relabelGoal_substGoal_comm]
              _ = substGoal (relabelGoal τ g') 0 (τ a') := by
                    rw [relabelGoal_substGoal_comm]
              _ = substGoal g' 0 c := by
                    simp [hτg, τ, a', c, swapAtoms]
          have hfuel' : search fuel P' (substGoal g' 0 c) = true := by
            simpa [hPσ, hgσ] using hfuel
          exact ⟨fuel + 1, by
            simpa [search, relabelGoal, P', g', c] using hfuel'⟩

  private theorem derivesFromAny_to_search_relabel :
      ∀ {P : Program} {gs : List Goal} {a : AtomVar}, DerivesFromAny P gs a →
        ∀ {ρ : Atom → Atom}, Function.Injective ρ →
          ∃ fuel, searchAnyAssumption fuel (relabelProgram ρ P)
            (List.map (relabelGoal ρ) gs) (relabelAtomVar ρ a) = true
    | P, _ :: _, _, .here h, ρ, hρ =>
        by
          obtain ⟨fuel, hfuel⟩ := fires_to_search_relabel h hρ
          exact ⟨fuel, by simp [searchAnyAssumption, hfuel]⟩
    | P, _ :: _, _, .there h, ρ, hρ =>
        by
          obtain ⟨fuel, hfuel⟩ := derivesFromAny_to_search_relabel h hρ
          exact ⟨fuel, by simp [searchAnyAssumption, hfuel]⟩

  private theorem fires_to_search_relabel :
      ∀ {P : Program} {g : Goal} {a : AtomVar}, Fires P g a →
        ∀ {ρ : Atom → Atom}, Function.Injective ρ →
          ∃ fuel, fires fuel (relabelProgram ρ P) (relabelGoal ρ g) (relabelAtomVar ρ a) = true
    | P, .atom a, _, .atom, ρ, hρ =>
        by
          exact ⟨1, by simp [fires, relabelGoal, relabelAtomVar]⟩
    | P, .imp g₁ g₂, a, .imp h₁ h₂, ρ, hρ =>
        by
          obtain ⟨fuel₁, h₁fuel⟩ := derives_to_search_relabel h₁ hρ
          obtain ⟨fuel₂, h₂fuel⟩ := fires_to_search_relabel h₂ hρ
          let P' := relabelProgram ρ P
          let g₁' := relabelGoal ρ g₁
          let g₂' := relabelGoal ρ g₂
          let a' := relabelAtomVar ρ a
          have h₁mono : search (fuel₁ + fuel₂) P' g₁' = true :=
            search_fuel_mono fuel₁ fuel₂ P' g₁' h₁fuel
          have h₂mono : fires (fuel₁ + fuel₂) P' g₂' a' = true := by
            simpa [Nat.add_comm] using fires_fuel_mono fuel₂ fuel₁ P' g₂' a' h₂fuel
          exact ⟨fuel₁ + fuel₂ + 1, by
            simpa [fires, relabelGoal, relabelAtomVar, P', g₁', g₂', a', Bool.and_eq_true] using
              And.intro h₁mono h₂mono⟩
    | P, .all g, .atom _, .allAtom atm h, ρ, hρ =>
        by
          obtain ⟨fuel, hfuel⟩ := fires_to_search_relabel h hρ
          let P' := relabelProgram ρ P
          let g' := relabelGoal ρ g
          have hfuel' : fires fuel P' (substGoal g' 0 (ρ atm)) (.atom (ρ atm)) = true := by
            simpa [P', g', relabelGoal_substGoal_comm, relabelAtomVar] using hfuel
          exact ⟨fuel + 1, by
            simpa [fires, relabelGoal, relabelAtomVar, P', g'] using hfuel'⟩
    | P, .all g, .bvar k, .allBvar atm freshP freshG h, ρ, hρ =>
        by
          let P' := relabelProgram ρ P
          let g' := relabelGoal ρ g
          let a' := ρ atm
          let c := freshAtomForGoal P' g'
          let τ : Atom → Atom := swapAtoms a' c
          let σ : Atom → Atom := τ ∘ ρ
          have hσ : Function.Injective σ := (swapAtoms_injective a' c).comp hρ
          have ha'P : a' ∉ programAtoms P' := relabelProgram_fresh hρ freshP
          have ha'g : a' ∉ goalAtoms g' := relabelGoal_fresh hρ freshG
          have hcP : c ∉ programAtoms P' := (freshAtomForGoal_fresh P' g').1
          have hcg : c ∉ goalAtoms g' := (freshAtomForGoal_fresh P' g').2
          have hτP : relabelProgram τ P' = P' := swapAtoms_program_id_of_fresh ha'P hcP
          have hτg : relabelGoal τ g' = g' := swapAtoms_goal_id_of_fresh ha'g hcg
          obtain ⟨fuel, hfuel⟩ := fires_to_search_relabel h hσ
          have hPσ : relabelProgram σ P = P' := by
            rw [show σ = τ ∘ ρ by rfl]
            rw [← relabelProgram_comp (ρ := ρ) (σ := τ) (P := P)]
            simpa [P'] using hτP
          have hgσ :
              relabelGoal σ (substGoal g 0 atm) = substGoal g' 0 c := by
            rw [show σ = τ ∘ ρ by rfl]
            rw [← relabelGoal_comp (ρ := ρ) (σ := τ) (g := substGoal g 0 atm)]
            calc
              relabelGoal τ (relabelGoal ρ (substGoal g 0 atm))
                  = relabelGoal τ (substGoal g' 0 a') := by
                      simp [g', a', relabelGoal_substGoal_comm]
              _ = substGoal (relabelGoal τ g') 0 (τ a') := by
                    rw [relabelGoal_substGoal_comm]
              _ = substGoal g' 0 c := by
                    simp [hτg, τ, a', c, swapAtoms]
          have hfuel' : fires fuel P' (substGoal g' 0 c) (.bvar k) = true := by
            simpa [hPσ, hgσ, relabelAtomVar] using hfuel
          exact ⟨fuel + 1, by
            simpa [fires, relabelGoal, relabelAtomVar, P', g', c] using hfuel'⟩
end

theorem derives_to_search {P : Program} {g : Goal} :
    Derives P g → SearchSupports P g := by
  intro h
  have hPid : relabelProgram id P = P := by
    apply relabelProgram_id_of_fixed
    intro a ha
    rfl
  have hgid : relabelGoal id g = g := by
    apply relabelGoal_id_of_fixed
    intro a ha
    rfl
  simpa [hPid, hgid] using derives_to_search_relabel h (ρ := id) (by
    intro a b hab
    simpa using hab)

theorem fires_to_search {P : Program} {g : Goal} {a : AtomVar} :
    Fires P g a → ∃ fuel, fires fuel P g a = true := by
  intro h
  have hPid : relabelProgram id P = P := by
    apply relabelProgram_id_of_fixed
    intro b hb
    rfl
  have hgid : relabelGoal id g = g := by
    apply relabelGoal_id_of_fixed
    intro b hb
    rfl
  have haid : relabelAtomVar id a = a := by
    cases a <;> rfl
  simpa [hPid, hgid, haid] using fires_to_search_relabel h (ρ := id) (by
    intro b c hbc
    simpa using hbc)

theorem derives_iff_searchSupports {P : Program} {g : Goal} :
    Derives P g ↔ SearchSupports P g := by
  constructor
  · exact derives_to_search
  · intro h
    rcases h with ⟨fuel, hfuel⟩
    exact search_to_derives hfuel

theorem derivesFromAny_of_mem {P : Program} {gs : List Goal} {g : Goal} {a : AtomVar}
    (hg : g ∈ gs) (hf : Fires P g a) :
    DerivesFromAny P gs a := by
  induction gs with
  | nil =>
      cases hg
  | cons g' rest ih =>
      simp at hg
      rcases hg with rfl | hg
      · exact DerivesFromAny.here hf
      · exact DerivesFromAny.there (ih hg)

theorem derives_self_support_atom {P : Program} {a : AtomVar}
    (ha : Goal.atom a ∈ P) :
    Derives P (.atom a) := by
  exact Derives.atom (derivesFromAny_of_mem ha Fires.atom)

theorem derives_atom_of_imp_mem {P : Program} {g : Goal} {a : AtomVar}
    (hg : Derives P g) (hmem : Goal.imp g (.atom a) ∈ P) :
    Derives P (.atom a) := by
  apply Derives.atom
  apply derivesFromAny_of_mem hmem
  exact Fires.imp hg Fires.atom

/-- Inversion for derivations of implication goals. -/
theorem derives_imp_inversion {P : Program} {g₁ g₂ : Goal}
    (hDer : Derives P (.imp g₁ g₂)) :
    Derives (g₁ :: P) g₂ := by
  cases hDer with
  | imp hBody =>
      exact hBody

/-- Inversion for derivations of conjunction goals. -/
theorem derives_conj_inversion {P : Program} {g₁ g₂ : Goal}
    (hDer : Derives P (.conj g₁ g₂)) :
    Derives P g₁ ∧ Derives P g₂ := by
  cases hDer with
  | conj h₁ h₂ =>
      exact ⟨h₁, h₂⟩

/-- Inversion for derivations of disjunction goals. -/
theorem derives_disj_inversion {P : Program} {g₁ g₂ : Goal}
    (hDer : Derives P (.disj g₁ g₂)) :
    Derives P g₁ ∨ Derives P g₂ := by
  cases hDer with
  | disjLeft h =>
      exact Or.inl h
  | disjRight h =>
      exact Or.inr h

private theorem atomVarAtoms_substAtomVar_avoids_atom
    {a atm : Atom} {n : Nat} {v : AtomVar}
    (ha : a ∉ atomVarAtoms v) (hatm : atm ≠ a) :
    a ∉ atomVarAtoms (substAtomVar n atm v) := by
  cases v with
  | atom b =>
      simpa [substAtomVar, atomVarAtoms] using ha
  | bvar k =>
      by_cases hk : k = n
      · simp [substAtomVar, atomVarAtoms, hk]
        intro h
        exact hatm h.symm
      · simp [substAtomVar, atomVarAtoms, hk]

private theorem goalAtoms_substGoal_avoids_atom
    {g : Goal} {a atm : Atom} {n : Nat}
    (ha : a ∉ goalAtoms g) (hatm : atm ≠ a) :
    a ∉ goalAtoms (substGoal g n atm) := by
  induction g generalizing n with
  | atom v =>
      simpa [goalAtoms, substGoal] using
        atomVarAtoms_substAtomVar_avoids_atom (a := a) (atm := atm) (n := n) (v := v)
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

theorem searchSupports_of_program_memeq {P Q : Program} {g : Goal}
    (hPQ : ∀ x, x ∈ P ↔ x ∈ Q) :
    SearchSupports P g → SearchSupports Q g := by
  rintro ⟨fuel, hfuel⟩
  exact ⟨fuel, search_mono_program fuel P Q g (fun x hx => (hPQ x).1 hx) hfuel⟩

theorem derives_of_program_memeq {P Q : Program} {g : Goal}
    (hPQ : ∀ x, x ∈ P ↔ x ∈ Q) :
    Derives P g → Derives Q g := by
  intro h
  exact derives_iff_searchSupports.mpr <|
    searchSupports_of_program_memeq hPQ (derives_iff_searchSupports.mp h)

theorem derives_mono_program {P Q : Program} {g : Goal}
    (hPQ : ∀ x, x ∈ P → x ∈ Q) :
    Derives P g → Derives Q g := by
  intro h
  rcases derives_iff_searchSupports.mp h with ⟨fuel, hfuel⟩
  exact derives_iff_searchSupports.mpr <|
    ⟨fuel, search_mono_program fuel P Q g hPQ hfuel⟩

theorem derives_weaken {P : Program} {extras : List Goal} {g : Goal} :
    Derives P g → Derives (extras ++ P) g := by
  intro h
  exact derives_mono_program
    (P := P) (Q := extras ++ P) (g := g)
    (fun x hx => List.mem_append.mpr (Or.inr hx)) h

private theorem mem_append_cons_cut {Q : List Goal} {d : Goal} {P : Program} {g : Goal} :
    g ∈ Q ++ d :: P ↔ g = d ∨ g ∈ Q ++ P := by
  induction Q with
  | nil =>
      simp
  | cons q qs ih =>
      simp [ih, or_left_comm, or_comm]

mutual
  private theorem search_strengthen_fresh_head_step {K : Goal} {a : Atom}
      (haK : a ∈ goalAtoms K)
      (hK_fires_only_a : ∀ {P : Program} {v : AtomVar}, Fires P K v → v = .atom a)
      (fuel : Nat) :
      (∀ (P : Program) (g : Goal),
        a ∉ goalAtoms g →
        a ∉ programAtoms P →
        search fuel (K :: P) g = true →
        search fuel P g = true) ∧
      (∀ (P : Program) (gs : List Goal) (v : AtomVar),
        a ∉ atomVarAtoms v →
        a ∉ programAtoms P →
        (∀ x, x ∈ gs → x ∈ P) →
        searchAnyAssumption fuel (K :: P) gs v = true →
        searchAnyAssumption fuel P gs v = true) ∧
      (∀ (P : Program) (g : Goal) (v : AtomVar),
        a ∉ goalAtoms g →
        a ∉ atomVarAtoms v →
        a ∉ programAtoms P →
        fires fuel (K :: P) g v = true →
        fires fuel P g v = true) := by
    induction fuel with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · intro P g haG haP h
          simp [search] at h
        · intro P gs v hva haP hgs h
          induction gs with
          | nil =>
              simp [searchAnyAssumption] at h
          | cons g rest ih =>
              have hRest : searchAnyAssumption 0 (K :: P) rest v = true := by
                simpa [searchAnyAssumption, fires] using h
              have hRestKeep :=
                ih (by
                  intro x hx
                  exact hgs x (by simp [hx])) hRest
              simpa [searchAnyAssumption, fires] using hRestKeep
        · intro P g v haG hva haP h
          simp [fires] at h
    | succ fuel ih =>
        obtain ⟨ihSearch, ihAny, ihFires⟩ := ih
        have hFires :
            ∀ (P : Program) (g : Goal) (v : AtomVar),
              a ∉ goalAtoms g →
              a ∉ atomVarAtoms v →
              a ∉ programAtoms P →
              fires (fuel + 1) (K :: P) g v = true →
              fires (fuel + 1) P g v = true := by
          intro P g v haG hva haP h
          cases g with
          | atom b =>
              simpa [fires] using h
          | imp g₁ g₂ =>
              have ha₁ : a ∉ goalAtoms g₁ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              have ha₂ : a ∉ goalAtoms g₂ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              simp [fires, Bool.and_eq_true] at h ⊢
              exact ⟨ihSearch P g₁ ha₁ haP h.1, ihFires P g₂ v ha₂ hva haP h.2⟩
          | conj g₁ g₂ =>
              simp [fires] at h
          | disj g₁ g₂ =>
              simp [fires] at h
          | all g =>
              cases v with
              | atom atm =>
                  have hatm : atm ≠ a := by
                    intro hEq
                    exact hva (by simp [atomVarAtoms, hEq])
                  have haBody : a ∉ goalAtoms g := by
                    simpa [goalAtoms] using haG
                  have hSub :
                      fires fuel (K :: P) (substGoal g 0 atm) (.atom atm) = true := by
                    simpa [fires] using h
                  have hKeep :=
                    ihFires P (substGoal g 0 atm) (.atom atm)
                      (goalAtoms_substGoal_avoids_atom (a := a) (atm := atm) (n := 0) haBody hatm)
                      (by simpa [atomVarAtoms] using hva)
                      haP hSub
                  simpa [fires] using hKeep
              | bvar k =>
                  let c := freshAtomForGoal (K :: P) g
                  let c' := freshAtomForGoal P g
                  let τ : Atom → Atom := swapAtoms c c'
                  have haBody : a ∉ goalAtoms g := by
                    simpa [goalAtoms] using haG
                  have haKProg : a ∈ programAtoms (K :: P) :=
                    mem_programAtoms_of_mem_goal (by simp) haK
                  have hc_ne : c ≠ a := by
                    intro hEq
                    exact (freshAtomForGoal_fresh (K :: P) g).1 <| by
                      simpa [c, hEq] using haKProg
                  have hcP : c ∉ programAtoms P := by
                    intro hm
                    exact (freshAtomForGoal_fresh (K :: P) g).1 <| by
                      simpa [programAtoms] using List.mem_append.mpr (Or.inr hm)
                  have hcg : c ∉ goalAtoms g := (freshAtomForGoal_fresh (K :: P) g).2
                  have hc'P : c' ∉ programAtoms P := (freshAtomForGoal_fresh P g).1
                  have hc'g : c' ∉ goalAtoms g := (freshAtomForGoal_fresh P g).2
                  have hτP : relabelProgram τ P = P :=
                    swapAtoms_program_id_of_fresh hcP hc'P
                  have hτg : relabelGoal τ g = g :=
                    swapAtoms_goal_id_of_fresh hcg hc'g
                  have hSub :
                      fires fuel (K :: P) (substGoal g 0 c) (.bvar k) = true := by
                    simpa [fires, c] using h
                  have hKeepBig :=
                    ihFires P (substGoal g 0 c) (.bvar k)
                      (goalAtoms_substGoal_avoids_atom (a := a) (atm := c) (n := 0) haBody hc_ne)
                      hva haP hSub
                  have hRename :
                      fires fuel P (substGoal g 0 c') (.bvar k) =
                        fires fuel P (substGoal g 0 c) (.bvar k) := by
                    simpa [τ, c, c', hτP, hτg, relabelGoal_substGoal_comm, relabelAtomVar, swapAtoms] using
                      fires_equivariant fuel P (substGoal g 0 c) (.bvar k) τ
                        (swapAtoms_injective c c')
                  have hKeepSmall : fires fuel P (substGoal g 0 c') (.bvar k) = true := by
                    rw [hRename]
                    exact hKeepBig
                  simpa [fires, c'] using hKeepSmall
        have hAny :
            ∀ (P : Program) (gs : List Goal) (v : AtomVar),
              a ∉ atomVarAtoms v →
              a ∉ programAtoms P →
              (∀ x, x ∈ gs → x ∈ P) →
              searchAnyAssumption (fuel + 1) (K :: P) gs v = true →
              searchAnyAssumption (fuel + 1) P gs v = true := by
          intro P gs v hva haP hgs h
          induction gs with
          | nil =>
              simp [searchAnyAssumption] at h
          | cons g rest ihGs =>
              simp [searchAnyAssumption, Bool.or_eq_true] at h
              rcases h with h | h
              · have hgP : g ∈ P := hgs g (by simp)
                have haG : a ∉ goalAtoms g := by
                  intro hm
                  exact haP (mem_programAtoms_of_mem_goal hgP hm)
                exact searchAnyAssumption_of_mem_fires (g := g) (a := v) (hg := by simp) <|
                  hFires P g v haG hva haP h
              · have hRestP : ∀ x, x ∈ rest → x ∈ P := by
                  intro x hx
                  exact hgs x (by simp [hx])
                simpa [searchAnyAssumption] using Or.inr (ihGs hRestP h)
        have hSearch :
            ∀ (P : Program) (g : Goal),
              a ∉ goalAtoms g →
              a ∉ programAtoms P →
              search (fuel + 1) (K :: P) g = true →
              search (fuel + 1) P g = true := by
          intro P g haG haP h
          cases g with
          | atom v =>
              have hva : a ∉ atomVarAtoms v := by
                simpa [goalAtoms] using haG
              have hSAA : searchAnyAssumption fuel (K :: P) (K :: P) v = true := by
                simpa [search] using h
              simp [searchAnyAssumption, Bool.or_eq_true] at hSAA
              rcases hSAA with hHead | hTail
              · have hv : v = .atom a := hK_fires_only_a (fires_to_derives hHead)
                subst hv
                exfalso
                exact hva (by simp [atomVarAtoms])
              · have hTailKeep :=
                  ihAny P P v hva haP (by
                    intro x hx
                    exact hx) hTail
                simpa [search] using hTailKeep
          | imp g₁ g₂ =>
              have ha₁ : a ∉ goalAtoms g₁ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              have ha₂ : a ∉ goalAtoms g₂ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              have haCons : a ∉ programAtoms (g₁ :: P) := by
                simpa [programAtoms] using And.intro ha₁ haP
              have hSub : search fuel (g₁ :: K :: P) g₂ = true := by
                simpa [search] using h
              have hPerm : search fuel (K :: g₁ :: P) g₂ = true := by
                apply search_mono_program fuel (g₁ :: K :: P) (K :: g₁ :: P) g₂
                · intro x hx
                  simp [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · exact Or.inr (Or.inl rfl)
                  · rcases hx with rfl | hx
                    · exact Or.inl rfl
                    · exact Or.inr (Or.inr hx)
                · exact hSub
              have hKeep := ihSearch (g₁ :: P) g₂ ha₂ haCons hPerm
              simpa [search] using hKeep
          | conj g₁ g₂ =>
              have ha₁ : a ∉ goalAtoms g₁ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              have ha₂ : a ∉ goalAtoms g₂ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              simp [search, Bool.and_eq_true] at h ⊢
              exact ⟨ihSearch P g₁ ha₁ haP h.1, ihSearch P g₂ ha₂ haP h.2⟩
          | disj g₁ g₂ =>
              have ha₁ : a ∉ goalAtoms g₁ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              have ha₂ : a ∉ goalAtoms g₂ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              simp [search, Bool.or_eq_true] at h ⊢
              rcases h with h | h
              · exact Or.inl (ihSearch P g₁ ha₁ haP h)
              · exact Or.inr (ihSearch P g₂ ha₂ haP h)
          | all g =>
              let c := freshAtomForGoal (K :: P) g
              let c' := freshAtomForGoal P g
              let τ : Atom → Atom := swapAtoms c c'
              have haBody : a ∉ goalAtoms g := by
                simpa [goalAtoms] using haG
              have haKProg : a ∈ programAtoms (K :: P) :=
                mem_programAtoms_of_mem_goal (by simp) haK
              have hc_ne : c ≠ a := by
                intro hEq
                exact (freshAtomForGoal_fresh (K :: P) g).1 <| by
                  simpa [c, hEq] using haKProg
              have hcP : c ∉ programAtoms P := by
                intro hm
                exact (freshAtomForGoal_fresh (K :: P) g).1 <| by
                  simpa [programAtoms] using List.mem_append.mpr (Or.inr hm)
              have hcg : c ∉ goalAtoms g := (freshAtomForGoal_fresh (K :: P) g).2
              have hc'P : c' ∉ programAtoms P := (freshAtomForGoal_fresh P g).1
              have hc'g : c' ∉ goalAtoms g := (freshAtomForGoal_fresh P g).2
              have hτP : relabelProgram τ P = P :=
                swapAtoms_program_id_of_fresh hcP hc'P
              have hτg : relabelGoal τ g = g :=
                swapAtoms_goal_id_of_fresh hcg hc'g
              have hSub :
                  search fuel (K :: P) (substGoal g 0 c) = true := by
                simpa [search, c] using h
              have hKeepBig :=
                ihSearch P (substGoal g 0 c)
                  (goalAtoms_substGoal_avoids_atom (a := a) (atm := c) (n := 0) haBody hc_ne)
                  haP hSub
              have hRename :
                  search fuel P (substGoal g 0 c') =
                    search fuel P (substGoal g 0 c) := by
                simpa [τ, c, c', hτP, hτg, relabelGoal_substGoal_comm, swapAtoms] using
                  search_equivariant fuel P (substGoal g 0 c) τ (swapAtoms_injective c c')
              have hKeepSmall : search fuel P (substGoal g 0 c') = true := by
                rw [hRename]
                exact hKeepBig
              simpa [search, c'] using hKeepSmall
        exact ⟨hSearch, hAny, hFires⟩
end

theorem search_strengthen_fresh_head {K : Goal} {a : Atom}
    (haK : a ∈ goalAtoms K)
    (hK_fires_only_a : ∀ {P : Program} {v : AtomVar}, Fires P K v → v = .atom a)
    (fuel : Nat) (P : Program) (g : Goal)
    (haG : a ∉ goalAtoms g)
    (haP : a ∉ programAtoms P) :
    search fuel (K :: P) g = true → search fuel P g = true :=
  (search_strengthen_fresh_head_step (haK := haK) (hK_fires_only_a := hK_fires_only_a) fuel).1
    P g haG haP

mutual
  private theorem search_strengthen_two_fresh_heads_step {Kφ Kψ : Goal} {a : Atom}
      (haKφ : a ∈ goalAtoms Kφ)
      (haKψ : a ∈ goalAtoms Kψ)
      (hKφ_fires_only_a : ∀ {P : Program} {v : AtomVar}, Fires P Kφ v → v = .atom a)
      (hKψ_fires_only_a : ∀ {P : Program} {v : AtomVar}, Fires P Kψ v → v = .atom a)
      (fuel : Nat) :
      (∀ (P : Program) (g : Goal),
        a ∉ goalAtoms g →
        a ∉ programAtoms P →
        search fuel (Kψ :: Kφ :: P) g = true →
        search fuel P g = true) ∧
      (∀ (P : Program) (gs : List Goal) (v : AtomVar),
        a ∉ atomVarAtoms v →
        a ∉ programAtoms P →
        (∀ x, x ∈ gs → x ∈ P) →
        searchAnyAssumption fuel (Kψ :: Kφ :: P) gs v = true →
        searchAnyAssumption fuel P gs v = true) ∧
      (∀ (P : Program) (g : Goal) (v : AtomVar),
        a ∉ goalAtoms g →
        a ∉ atomVarAtoms v →
        a ∉ programAtoms P →
        fires fuel (Kψ :: Kφ :: P) g v = true →
        fires fuel P g v = true) := by
    induction fuel with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · intro P g haG haP h
          simp [search] at h
        · intro P gs v hva haP hgs h
          induction gs with
          | nil =>
              simp [searchAnyAssumption] at h
          | cons g rest ih =>
              have hRest : searchAnyAssumption 0 (Kψ :: Kφ :: P) rest v = true := by
                simpa [searchAnyAssumption, fires] using h
              have hRestKeep :=
                ih (by
                  intro x hx
                  exact hgs x (by simp [hx])) hRest
              simpa [searchAnyAssumption, fires] using hRestKeep
        · intro P g v haG hva haP h
          simp [fires] at h
    | succ fuel ih =>
        obtain ⟨ihSearch, ihAny, ihFires⟩ := ih
        have hFires :
            ∀ (P : Program) (g : Goal) (v : AtomVar),
              a ∉ goalAtoms g →
              a ∉ atomVarAtoms v →
              a ∉ programAtoms P →
              fires (fuel + 1) (Kψ :: Kφ :: P) g v = true →
              fires (fuel + 1) P g v = true := by
          intro P g v haG hva haP h
          cases g with
          | atom b =>
              simpa [fires] using h
          | imp g₁ g₂ =>
              have ha₁ : a ∉ goalAtoms g₁ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              have ha₂ : a ∉ goalAtoms g₂ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              simp [fires, Bool.and_eq_true] at h ⊢
              exact ⟨ihSearch P g₁ ha₁ haP h.1, ihFires P g₂ v ha₂ hva haP h.2⟩
          | conj g₁ g₂ =>
              simp [fires] at h
          | disj g₁ g₂ =>
              simp [fires] at h
          | all g =>
              cases v with
              | atom atm =>
                  have hatm : atm ≠ a := by
                    intro hEq
                    exact hva (by simp [atomVarAtoms, hEq])
                  have haBody : a ∉ goalAtoms g := by
                    simpa [goalAtoms] using haG
                  have hSub :
                      fires fuel (Kψ :: Kφ :: P) (substGoal g 0 atm) (.atom atm) = true := by
                    simpa [fires] using h
                  have hKeep :=
                    ihFires P (substGoal g 0 atm) (.atom atm)
                      (goalAtoms_substGoal_avoids_atom (a := a) (atm := atm) (n := 0) haBody hatm)
                      (by simpa [atomVarAtoms] using hva)
                      haP hSub
                  simpa [fires] using hKeep
              | bvar k =>
                  let c := freshAtomForGoal (Kψ :: Kφ :: P) g
                  let c' := freshAtomForGoal P g
                  let τ : Atom → Atom := swapAtoms c c'
                  have haBody : a ∉ goalAtoms g := by
                    simpa [goalAtoms] using haG
                  have haKProg : a ∈ programAtoms (Kψ :: Kφ :: P) :=
                    mem_programAtoms_of_mem_goal (by simp) haKψ
                  have hc_ne : c ≠ a := by
                    intro hEq
                    exact (freshAtomForGoal_fresh (Kψ :: Kφ :: P) g).1 <| by
                      simpa [c, hEq] using haKProg
                  have hcP : c ∉ programAtoms P := by
                    intro hm
                    exact (freshAtomForGoal_fresh (Kψ :: Kφ :: P) g).1 <| by
                      simpa [programAtoms] using List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hm)))
                  have hcg : c ∉ goalAtoms g := (freshAtomForGoal_fresh (Kψ :: Kφ :: P) g).2
                  have hc'P : c' ∉ programAtoms P := (freshAtomForGoal_fresh P g).1
                  have hc'g : c' ∉ goalAtoms g := (freshAtomForGoal_fresh P g).2
                  have hτP : relabelProgram τ P = P :=
                    swapAtoms_program_id_of_fresh hcP hc'P
                  have hτg : relabelGoal τ g = g :=
                    swapAtoms_goal_id_of_fresh hcg hc'g
                  have hSub :
                      fires fuel (Kψ :: Kφ :: P) (substGoal g 0 c) (.bvar k) = true := by
                    simpa [fires, c] using h
                  have hKeepBig :=
                    ihFires P (substGoal g 0 c) (.bvar k)
                      (goalAtoms_substGoal_avoids_atom (a := a) (atm := c) (n := 0) haBody hc_ne)
                      hva haP hSub
                  have hRename :
                      fires fuel P (substGoal g 0 c') (.bvar k) =
                        fires fuel P (substGoal g 0 c) (.bvar k) := by
                    simpa [τ, c, c', hτP, hτg, relabelGoal_substGoal_comm, relabelAtomVar, swapAtoms] using
                      fires_equivariant fuel P (substGoal g 0 c) (.bvar k) τ
                        (swapAtoms_injective c c')
                  have hKeepSmall : fires fuel P (substGoal g 0 c') (.bvar k) = true := by
                    rw [hRename]
                    exact hKeepBig
                  simpa [fires, c'] using hKeepSmall
        have hAny :
            ∀ (P : Program) (gs : List Goal) (v : AtomVar),
              a ∉ atomVarAtoms v →
              a ∉ programAtoms P →
              (∀ x, x ∈ gs → x ∈ P) →
              searchAnyAssumption (fuel + 1) (Kψ :: Kφ :: P) gs v = true →
              searchAnyAssumption (fuel + 1) P gs v = true := by
          intro P gs v hva haP hgs h
          induction gs with
          | nil =>
              simp [searchAnyAssumption] at h
          | cons g rest ihGs =>
              simp [searchAnyAssumption, Bool.or_eq_true] at h
              rcases h with h | h
              · have hgP : g ∈ P := hgs g (by simp)
                have haG : a ∉ goalAtoms g := by
                  intro hm
                  exact haP (mem_programAtoms_of_mem_goal hgP hm)
                exact searchAnyAssumption_of_mem_fires (g := g) (a := v) (hg := by simp) <|
                  hFires P g v haG hva haP h
              · have hRestP : ∀ x, x ∈ rest → x ∈ P := by
                  intro x hx
                  exact hgs x (by simp [hx])
                simpa [searchAnyAssumption] using Or.inr (ihGs hRestP h)
        have hSearch :
            ∀ (P : Program) (g : Goal),
              a ∉ goalAtoms g →
              a ∉ programAtoms P →
              search (fuel + 1) (Kψ :: Kφ :: P) g = true →
              search (fuel + 1) P g = true := by
          intro P g haG haP h
          cases g with
          | atom v =>
              have hva : a ∉ atomVarAtoms v := by
                simpa [goalAtoms] using haG
              have hSAA : searchAnyAssumption fuel (Kψ :: Kφ :: P) (Kψ :: Kφ :: P) v = true := by
                simpa [search] using h
              simp [searchAnyAssumption, Bool.or_eq_true] at hSAA
              rcases hSAA with hHead | hTail
              · have hv : v = .atom a := hKψ_fires_only_a (fires_to_derives hHead)
                subst hv
                exfalso
                exact hva (by simp [atomVarAtoms])
              · have hTail' :
                    fires fuel (Kψ :: Kφ :: P) Kφ v = true ∨
                      searchAnyAssumption fuel (Kψ :: Kφ :: P) P v = true := by
                  simpa [searchAnyAssumption, Bool.or_eq_true] using hTail
                rcases hTail' with hHead | hRest
                · have hv : v = .atom a := hKφ_fires_only_a (fires_to_derives hHead)
                  subst hv
                  exfalso
                  exact hva (by simp [atomVarAtoms])
                · have hRestKeep :=
                    ihAny P P v hva haP (by
                      intro x hx
                      exact hx) hRest
                  simpa [search] using hRestKeep
          | imp g₁ g₂ =>
              have ha₁ : a ∉ goalAtoms g₁ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              have ha₂ : a ∉ goalAtoms g₂ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              have haCons : a ∉ programAtoms (g₁ :: P) := by
                simpa [programAtoms] using And.intro ha₁ haP
              have hSub : search fuel (g₁ :: Kψ :: Kφ :: P) g₂ = true := by
                simpa [search] using h
              have hPerm : search fuel (Kψ :: Kφ :: g₁ :: P) g₂ = true := by
                apply search_mono_program fuel (g₁ :: Kψ :: Kφ :: P) (Kψ :: Kφ :: g₁ :: P) g₂
                · intro x hx
                  simp [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · exact Or.inr (Or.inr (Or.inl rfl))
                  · rcases hx with rfl | hx
                    · exact Or.inl rfl
                    · rcases hx with rfl | hx
                      · exact Or.inr (Or.inl rfl)
                      · exact Or.inr (Or.inr (Or.inr hx))
                · exact hSub
              have hKeep := ihSearch (g₁ :: P) g₂ ha₂ haCons hPerm
              simpa [search] using hKeep
          | conj g₁ g₂ =>
              have ha₁ : a ∉ goalAtoms g₁ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              have ha₂ : a ∉ goalAtoms g₂ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              simp [search, Bool.and_eq_true] at h ⊢
              exact ⟨ihSearch P g₁ ha₁ haP h.1, ihSearch P g₂ ha₂ haP h.2⟩
          | disj g₁ g₂ =>
              have ha₁ : a ∉ goalAtoms g₁ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              have ha₂ : a ∉ goalAtoms g₂ := by
                intro hm
                exact haG (by simp [goalAtoms, hm])
              simp [search, Bool.or_eq_true] at h ⊢
              rcases h with h | h
              · exact Or.inl (ihSearch P g₁ ha₁ haP h)
              · exact Or.inr (ihSearch P g₂ ha₂ haP h)
          | all g =>
              let c := freshAtomForGoal (Kψ :: Kφ :: P) g
              let c' := freshAtomForGoal P g
              let τ : Atom → Atom := swapAtoms c c'
              have haBody : a ∉ goalAtoms g := by
                simpa [goalAtoms] using haG
              have haKProg : a ∈ programAtoms (Kψ :: Kφ :: P) :=
                mem_programAtoms_of_mem_goal (by simp) haKψ
              have hc_ne : c ≠ a := by
                intro hEq
                exact (freshAtomForGoal_fresh (Kψ :: Kφ :: P) g).1 <| by
                  simpa [c, hEq] using haKProg
              have hcP : c ∉ programAtoms P := by
                intro hm
                exact (freshAtomForGoal_fresh (Kψ :: Kφ :: P) g).1 <| by
                  simpa [programAtoms] using List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hm)))
              have hcg : c ∉ goalAtoms g := (freshAtomForGoal_fresh (Kψ :: Kφ :: P) g).2
              have hc'P : c' ∉ programAtoms P := (freshAtomForGoal_fresh P g).1
              have hc'g : c' ∉ goalAtoms g := (freshAtomForGoal_fresh P g).2
              have hτP : relabelProgram τ P = P :=
                swapAtoms_program_id_of_fresh hcP hc'P
              have hτg : relabelGoal τ g = g :=
                swapAtoms_goal_id_of_fresh hcg hc'g
              have hSub :
                  search fuel (Kψ :: Kφ :: P) (substGoal g 0 c) = true := by
                simpa [search, c] using h
              have hKeepBig :=
                ihSearch P (substGoal g 0 c)
                  (goalAtoms_substGoal_avoids_atom (a := a) (atm := c) (n := 0) haBody hc_ne)
                  haP hSub
              have hRename :
                  search fuel P (substGoal g 0 c') =
                    search fuel P (substGoal g 0 c) := by
                simpa [τ, c, c', hτP, hτg, relabelGoal_substGoal_comm, swapAtoms] using
                  search_equivariant fuel P (substGoal g 0 c) τ (swapAtoms_injective c c')
              have hKeepSmall : search fuel P (substGoal g 0 c') = true := by
                rw [hRename]
                exact hKeepBig
              simpa [search, c'] using hKeepSmall
        exact ⟨hSearch, hAny, hFires⟩
end

theorem search_strengthen_two_fresh_heads {Kφ Kψ : Goal} {a : Atom}
    (haKφ : a ∈ goalAtoms Kφ)
    (haKψ : a ∈ goalAtoms Kψ)
    (hKφ_fires_only_a : ∀ {P : Program} {v : AtomVar}, Fires P Kφ v → v = .atom a)
    (hKψ_fires_only_a : ∀ {P : Program} {v : AtomVar}, Fires P Kψ v → v = .atom a)
    (fuel : Nat) (P : Program) (g : Goal)
    (haG : a ∉ goalAtoms g)
    (haP : a ∉ programAtoms P) :
    search fuel (Kψ :: Kφ :: P) g = true → search fuel P g = true :=
  (search_strengthen_two_fresh_heads_step
    (haKφ := haKφ) (haKψ := haKψ)
    (hKφ_fires_only_a := hKφ_fires_only_a)
    (hKψ_fires_only_a := hKψ_fires_only_a) fuel).1
    P g haG haP

-- ============================================================
-- § Search Cut (Gheorghiu Lemma 2.8)
-- ============================================================

/-!
## Goal complexity measure

`goalComplexity` counts constructors with atoms/bvars as 1.
Key property: `goalComplexity (substGoal g n a) = goalComplexity g`.
-/

def goalComplexity : Goal → Nat
  | .atom _ => 1
  | .imp g₁ g₂ => 1 + goalComplexity g₁ + goalComplexity g₂
  | .conj g₁ g₂ => 1 + goalComplexity g₁ + goalComplexity g₂
  | .disj g₁ g₂ => 1 + goalComplexity g₁ + goalComplexity g₂
  | .all g => 1 + goalComplexity g

theorem goalComplexity_pos (g : Goal) : goalComplexity g ≥ 1 := by
  cases g <;> simp [goalComplexity] <;> omega

private theorem atomVarComplexity_substAtomVar (n : Nat) (a : Atom) (v : AtomVar) :
    goalComplexity (.atom (substAtomVar n a v)) = goalComplexity (.atom v) := by
  cases v with
  | atom _ => simp [goalComplexity]
  | bvar k =>
      by_cases h : k = n
      · subst h; rfl
      · simp [substAtomVar, h]

theorem goalComplexity_substGoal (g : Goal) (n : Nat) (a : Atom) :
    goalComplexity (substGoal g n a) = goalComplexity g := by
  induction g generalizing n with
  | atom v => exact atomVarComplexity_substAtomVar n a v
  | imp g₁ g₂ ih₁ ih₂ => simp [substGoal, goalComplexity, ih₁, ih₂]
  | conj g₁ g₂ ih₁ ih₂ => simp [substGoal, goalComplexity, ih₁, ih₂]
  | disj g₁ g₂ ih₁ ih₂ => simp [substGoal, goalComplexity, ih₁, ih₂]
  | all g ih => simp [substGoal, goalComplexity, ih]

/-!
## Universal elimination for fresh atoms

`Derives P (.all g) → Derives P (substGoal g 0 atm)` when `atm` is
fresh for `P` and `g`. This follows from equivariance (swap the
eigenvariable with atm).
-/

/-- Universal elimination for fresh atoms. -/
theorem derives_all_elim_fresh {P : Program} {g : Goal} {atm : Atom}
    (h : Derives P (.all g))
    (hatmP : atm ∉ programAtoms P) (hatmG : atm ∉ goalAtoms g) :
    Derives P (substGoal g 0 atm) := by
  have hSS := derives_iff_searchSupports.mp h
  obtain ⟨fuel, hfuel⟩ := hSS
  have hc := freshAtomForGoal_fresh P g
  have hSearch : ∃ f, search f P (substGoal g 0 (freshAtomForGoal P g)) = true := by
    cases fuel with
    | zero => simp [search] at hfuel
    | succ f => exact ⟨f, by simpa [search] using hfuel⟩
  obtain ⟨f, hf⟩ := hSearch
  let c := freshAtomForGoal P g
  have hτP := swapAtoms_program_id_of_fresh hc.1 hatmP
  have hτg := swapAtoms_goal_id_of_fresh hc.2 hatmG
  have hDerC := search_to_derives hf
  have hRel := derives_relabel (swapAtoms_injective c atm) hDerC
  rw [show relabelProgram (swapAtoms c atm) P = P from hτP] at hRel
  rwa [relabelGoal_substGoal_comm, hτg, swapAtoms_self_left] at hRel

/-- Any two fresh instantiations of the same body are derivationally equivalent. -/
theorem derives_substGoal_fresh_equiv {P : Program} {g : Goal} {a b : Atom}
    (haP : a ∉ programAtoms P) (haG : a ∉ goalAtoms g)
    (hbP : b ∉ programAtoms P) (hbG : b ∉ goalAtoms g) :
    Derives P (substGoal g 0 a) ↔ Derives P (substGoal g 0 b) := by
  constructor
  · intro h
    let τ : Atom → Atom := swapAtoms a b
    have hτP : relabelProgram τ P = P :=
      swapAtoms_program_id_of_fresh haP hbP
    have hτg : relabelGoal τ g = g :=
      swapAtoms_goal_id_of_fresh haG hbG
    have hRel := derives_relabel (swapAtoms_injective a b) h
    rw [show relabelProgram τ P = P from hτP] at hRel
    simpa [τ, relabelGoal_substGoal_comm, hτg, swapAtoms_self_left] using hRel
  · intro h
    let τ : Atom → Atom := swapAtoms a b
    have hτP : relabelProgram τ P = P :=
      swapAtoms_program_id_of_fresh haP hbP
    have hτg : relabelGoal τ g = g :=
      swapAtoms_goal_id_of_fresh haG hbG
    have hRel := derives_relabel (swapAtoms_injective a b) h
    rw [show relabelProgram τ P = P from hτP] at hRel
    simpa [τ, relabelGoal_substGoal_comm, hτg, swapAtoms_self_right] using hRel

/-- Search-level fresh instantiation, obtained from `derives_all_elim_fresh`. -/
theorem searchSupports_all_elim_fresh {P : Program} {g : Goal} {atm : Atom}
    (h : SearchSupports P (.all g))
    (hatmP : atm ∉ programAtoms P) (hatmG : atm ∉ goalAtoms g) :
    SearchSupports P (substGoal g 0 atm) := by
  exact derives_iff_searchSupports.mp <|
    derives_all_elim_fresh (derives_iff_searchSupports.mpr h) hatmP hatmG

/-- Any two fresh instantiations of the same body are search-equivalent. -/
theorem searchSupports_substGoal_fresh_equiv {P : Program} {g : Goal} {a b : Atom}
    (haP : a ∉ programAtoms P) (haG : a ∉ goalAtoms g)
    (hbP : b ∉ programAtoms P) (hbG : b ∉ goalAtoms g) :
    SearchSupports P (substGoal g 0 a) ↔ SearchSupports P (substGoal g 0 b) := by
  constructor
  · intro h
    exact derives_iff_searchSupports.mp <|
      (derives_substGoal_fresh_equiv haP haG hbP hbG).mp <|
        derives_iff_searchSupports.mpr h
  · intro h
    exact derives_iff_searchSupports.mp <|
      (derives_substGoal_fresh_equiv haP haG hbP hbG).mpr <|
        derives_iff_searchSupports.mpr h

/-- Inversion for derivations of universal goals. -/
theorem derives_all_inversion {P : Program} {g : Goal}
    (hDer : Derives P (.all g)) :
    ∃ a, a ∉ programAtoms P ∧ a ∉ goalAtoms g ∧ Derives P (substGoal g 0 a) := by
  cases hDer with
  | all a haP haG hsub =>
      exact ⟨a, haP, haG, hsub⟩

/-- The `.atom` firing branch of an `.all` goal exposes the matching instantiation directly. -/
theorem fires_all_atom_reduce {P : Program} {g : Goal} {atm : Atom}
    (hFire : Fires P (.all g) (.atom atm)) :
    Fires P (substGoal g 0 atm) (.atom atm) := by
  cases hFire with
  | allAtom _ hsub =>
      simpa using hsub

/-- The `.bvar` firing branch of an `.all` goal reduces to a fresh instantiated body. -/
theorem derives_and_fires_all_bvar_reduce {P : Program} {g : Goal} {k : Nat}
    (hDer : Derives P (.all g))
    (hFire : Fires P (.all g) (.bvar k)) :
    ∃ a, a ∉ programAtoms P ∧ a ∉ goalAtoms g ∧
      Derives P (substGoal g 0 a) ∧ Fires P (substGoal g 0 a) (.bvar k) := by
  cases hFire with
  | allBvar a haP haG hsub =>
      exact ⟨a, haP, haG, derives_all_elim_fresh hDer haP haG, hsub⟩

/-- The remaining `.all`/`.atom` blocker factors through a mixed fresh-vs-target body instance. -/
theorem derives_and_fires_all_atom_reduce_step {P : Program} {g : Goal} {atm : Atom}
    (hDer : Derives P (.all g))
    (hFire : Fires P (substGoal g 0 atm) (.atom atm)) :
    ∃ a, a ∉ programAtoms P ∧ a ∉ goalAtoms g ∧
      Derives P (substGoal g 0 a) ∧ Fires P (substGoal g 0 atm) (.atom atm) := by
  rcases derives_all_inversion hDer with ⟨a, haP, haG, hsub⟩
  exact ⟨a, haP, haG, hsub, hFire⟩

/-- Constant atom bodies are the trivial structural branch of the mixed blocker. -/
theorem derives_and_fires_subst_atom_const_reduce {P : Program} {b : Atom} {a atm : Atom}
    (hDer : Derives P (substGoal (.atom (.atom b)) 0 a))
    (hFire : Fires P (substGoal (.atom (.atom b)) 0 atm) (.atom atm)) :
    Derives P (.atom (.atom atm)) := by
  simp [substGoal] at hDer hFire ⊢
  cases hFire
  simpa using hDer

/-- Nonzero de Bruijn atom bodies cannot fire a free atom in the mixed blocker. -/
theorem fires_subst_atom_succ_bvar_atom_false {P : Program} {k : Nat} {atm : Atom} :
    ¬ Fires P (substGoal (.atom (.bvar (k + 1))) 0 atm) (.atom atm) := by
  intro h
  simp [substGoal] at h
  cases h

/-- Conjunction bodies never contribute to the mixed `.atom` firing branch. -/
theorem fires_subst_conj_atom_false {P : Program} {g₁ g₂ : Goal} {atm : Atom} :
    ¬ Fires P (substGoal (.conj g₁ g₂) 0 atm) (.atom atm) := by
  intro h
  simp [substGoal] at h
  cases h

/-- Disjunction bodies never contribute to the mixed `.atom` firing branch. -/
theorem fires_subst_disj_atom_false {P : Program} {g₁ g₂ : Goal} {atm : Atom} :
    ¬ Fires P (substGoal (.disj g₁ g₂) 0 atm) (.atom atm) := by
  intro h
  simp [substGoal] at h
  cases h

/-- Nested universal bodies reduce the mixed blocker to a shifted inner-body instance. -/
theorem derives_and_fires_subst_all_atom_reduce_step {P : Program} {g : Goal} {a atm : Atom}
    (hDer : Derives P (substGoal (.all g) 0 a))
    (hFire : Fires P (substGoal (.all g) 0 atm) (.atom atm)) :
    ∃ c, c ∉ programAtoms P ∧ c ∉ goalAtoms (substGoal g 1 a) ∧
      Derives P (substGoal (substGoal g 1 a) 0 c) ∧
      Fires P (substGoal (substGoal g 1 atm) 0 atm) (.atom atm) := by
  simp [substGoal] at hDer hFire
  rcases derives_all_inversion hDer with ⟨c, hcP, hcG, hsub⟩
  exact ⟨c, hcP, hcG, hsub, fires_all_atom_reduce hFire⟩

/-- Implication bodies reduce the mixed blocker to a composition obligation. -/
theorem derives_and_fires_subst_imp_atom_reduce_step
    {P : Program} {g₁ g₂ : Goal} {a atm : Atom}
    (hDer : Derives P (substGoal (.imp g₁ g₂) 0 a))
    (hFire : Fires P (substGoal (.imp g₁ g₂) 0 atm) (.atom atm)) :
    Derives (substGoal g₁ 0 a :: P) (substGoal g₂ 0 a) ∧
      Derives P (substGoal g₁ 0 atm) ∧
      Fires P (substGoal g₂ 0 atm) (.atom atm) := by
  simp [substGoal] at hDer hFire
  cases hDer with
  | imp hSub =>
      cases hFire with
      | imp hPrem hTail =>
          exact ⟨hSub, hPrem, hTail⟩

/-!
## Non-injective relabeling

The injective relabeling theorem `derives_relabel` requires `Function.Injective ρ` because
it maps the eigenvariable `a` to `ρ a` and needs `ρ a` to be fresh, which requires
injectivity to preserve non-membership.

The non-injective version uses a different strategy for the `.all` and `.allBvar` cases:
instead of mapping the eigenvariable through `ρ`, it defines a **redirected relabeling** `σ`
that agrees with `ρ` on all atoms in the program and goal (which don't include the
eigenvariable, by freshness) but maps the eigenvariable to a fresh atom in the target.
Since `σ` agrees with `ρ` on all relevant atoms, `relabelProgram σ P = relabelProgram ρ P`
and `relabelGoal σ g = relabelGoal ρ g`, so the recursive call lands exactly where needed.
-/

private theorem relabelAtomVar_ext {σ ρ : Atom → Atom} {v : AtomVar}
    (h : ∀ a, a ∈ atomVarAtoms v → σ a = ρ a) :
    relabelAtomVar σ v = relabelAtomVar ρ v := by
  cases v with
  | atom a =>
      have : σ a = ρ a := h a (by simp [atomVarAtoms])
      simp [relabelAtomVar, this]
  | bvar k =>
      simp [relabelAtomVar]

private theorem relabelGoal_ext {σ ρ : Atom → Atom} {g : Goal}
    (h : ∀ a, a ∈ goalAtoms g → σ a = ρ a) :
    relabelGoal σ g = relabelGoal ρ g := by
  induction g with
  | atom v =>
      simp [relabelGoal]
      exact relabelAtomVar_ext (by simpa [goalAtoms] using h)
  | imp g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal]
      exact ⟨ih₁ (fun a ha => h a (by simp [goalAtoms, ha])),
             ih₂ (fun a ha => h a (by simp [goalAtoms, ha]))⟩
  | conj g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal]
      exact ⟨ih₁ (fun a ha => h a (by simp [goalAtoms, ha])),
             ih₂ (fun a ha => h a (by simp [goalAtoms, ha]))⟩
  | disj g₁ g₂ ih₁ ih₂ =>
      simp [relabelGoal]
      exact ⟨ih₁ (fun a ha => h a (by simp [goalAtoms, ha])),
             ih₂ (fun a ha => h a (by simp [goalAtoms, ha]))⟩
  | all g ih =>
      simp [relabelGoal]
      exact ih (fun a ha => h a (by simpa [goalAtoms] using ha))

private theorem relabelProgram_ext {σ ρ : Atom → Atom} {P : Program}
    (h : ∀ a, a ∈ programAtoms P → σ a = ρ a) :
    relabelProgram σ P = relabelProgram ρ P := by
  induction P with
  | nil => rfl
  | cons g rest ih =>
      have hg : relabelGoal σ g = relabelGoal ρ g :=
        relabelGoal_ext (fun a ha => h a (by simp [programAtoms, ha]))
      have hrest : relabelProgram σ rest = relabelProgram ρ rest :=
        ih (fun a ha => h a (by
          have : a ∈ goalAtoms g ++ programAtoms rest := List.mem_append.mpr (Or.inr ha)
          simpa [programAtoms] using this))
      show relabelGoal σ g :: relabelProgram σ rest = relabelGoal ρ g :: relabelProgram ρ rest
      rw [hg, hrest]

mutual
  theorem derives_relabel_noninj (ρ : Atom → Atom) :
      ∀ {P : Program} {g : Goal},
        Derives P g → Derives (relabelProgram ρ P) (relabelGoal ρ g)
    | _, _, .atom h =>
        Derives.atom (derivesFromAny_relabel_noninj ρ h)
    | _, _, .imp h =>
        by
          simpa [relabelProgram, relabelGoal] using
            (Derives.imp (derives_relabel_noninj ρ h))
    | _, _, .conj h₁ h₂ =>
        Derives.conj (derives_relabel_noninj ρ h₁) (derives_relabel_noninj ρ h₂)
    | _, _, .disjLeft h =>
        Derives.disjLeft (derives_relabel_noninj ρ h)
    | _, _, .disjRight h =>
        Derives.disjRight (derives_relabel_noninj ρ h)
    | P, .all g, .all a haP hag hsub =>
        by
          let P' := relabelProgram ρ P
          let g' := relabelGoal ρ g
          let c' := freshAtomForGoal P' g'
          -- σ agrees with ρ on all atoms in P and g, but maps the eigenvariable a to c'
          let σ : Atom → Atom := fun x => if x = a then c' else ρ x
          have hσP : relabelProgram σ P = P' :=
            relabelProgram_ext (fun x hx => by
              simp [σ]
              intro hxa
              exact absurd (hxa ▸ hx) haP)
          have hσg : relabelGoal σ g = g' :=
            relabelGoal_ext (fun x hx => by
              simp [σ]
              intro hxa
              exact absurd (hxa ▸ hx) hag)
          have hσsub : relabelGoal σ (substGoal g 0 a) = substGoal g' 0 c' := by
            rw [relabelGoal_substGoal_comm, hσg]
            simp [σ]
          have ih := derives_relabel_noninj σ hsub
          rw [hσP, hσsub] at ih
          exact Derives.all c' (freshAtomForGoal_fresh P' g').1
            (freshAtomForGoal_fresh P' g').2 ih

  theorem derivesFromAny_relabel_noninj (ρ : Atom → Atom) :
      ∀ {P : Program} {gs : List Goal} {a : AtomVar},
        DerivesFromAny P gs a →
          DerivesFromAny (relabelProgram ρ P) (List.map (relabelGoal ρ) gs) (relabelAtomVar ρ a)
    | _, _, _, .here h =>
        by
          simp
          exact DerivesFromAny.here (fires_relabel_noninj ρ h)
    | _, _, _, .there h =>
        by
          simp
          exact DerivesFromAny.there (derivesFromAny_relabel_noninj ρ h)

  theorem fires_relabel_noninj (ρ : Atom → Atom) :
      ∀ {P : Program} {g : Goal} {a : AtomVar},
        Fires P g a → Fires (relabelProgram ρ P) (relabelGoal ρ g) (relabelAtomVar ρ a)
    | P, _, a, .atom =>
        by
          simpa [relabelGoal, relabelAtomVar] using
            (Fires.atom (P := relabelProgram ρ P) (a := relabelAtomVar ρ a))
    | _, _, _, .imp h₁ h₂ =>
        Fires.imp (derives_relabel_noninj ρ h₁) (fires_relabel_noninj ρ h₂)
    | P, .all g, _, .allAtom atm h =>
        by
          have h' :
              Fires (relabelProgram ρ P) (substGoal (relabelGoal ρ g) 0 (ρ atm)) (.atom (ρ atm)) := by
            simpa [relabelAtomVar, relabelGoal_substGoal_comm] using fires_relabel_noninj ρ h
          exact Fires.allAtom (ρ atm) h'
    | P, .all g, .bvar k, .allBvar atm freshP freshG h =>
        by
          let P' := relabelProgram ρ P
          let g' := relabelGoal ρ g
          let c' := freshAtomForGoal P' g'
          let σ : Atom → Atom := fun x => if x = atm then c' else ρ x
          have hσP : relabelProgram σ P = P' :=
            relabelProgram_ext (fun x hx => by
              simp [σ]
              intro hxa
              exact absurd (hxa ▸ hx) freshP)
          have hσg : relabelGoal σ g = g' :=
            relabelGoal_ext (fun x hx => by
              simp [σ]
              intro hxa
              exact absurd (hxa ▸ hx) freshG)
          have hσsub : relabelGoal σ (substGoal g 0 atm) = substGoal g' 0 c' := by
            rw [relabelGoal_substGoal_comm, hσg]
            simp [σ]
          have ih := fires_relabel_noninj σ h
          rw [hσP, hσsub] at ih
          simp [relabelAtomVar] at ih
          exact Fires.allBvar c' (freshAtomForGoal_fresh P' g').1
            (freshAtomForGoal_fresh P' g').2 ih
end

/-- Full universal elimination: any derivation of `.all g` gives a derivation of
the substituted body for ANY atom, not just fresh ones. This is the theorem that
was blocked for 15 attempts. -/
theorem derives_all_elim {P : Program} {g : Goal} (atm : Atom)
    (h : Derives P (.all g)) :
    Derives P (substGoal g 0 atm) := by
  rcases derives_all_inversion h with ⟨a, haP, hag, hsub⟩
  -- Apply non-injective relabeling with ρ = replaceAtom a atm
  have hDer := derives_relabel_noninj (replaceAtom a atm) hsub
  rwa [relabelProgram_id_of_absent haP,
       relabelGoal_substGoal_zero_replace hag] at hDer

private theorem derives_atom_of_mem_fires {P : Program} {g : Goal} {a : AtomVar}
    (hg : g ∈ P) (hf : Fires P g a) :
    Derives P (.atom a) :=
  Derives.atom (derivesFromAny_of_mem hg hf)

private theorem not_mem_programAtoms_of_mono_program {R S : Program} {a : Atom}
    (hSR : ∀ x, x ∈ S → x ∈ R) (haR : a ∉ programAtoms R) :
    a ∉ programAtoms S := by
  intro hm
  induction S with
  | nil =>
      cases hm
  | cons g rest ih =>
      simp [programAtoms] at hm
      rcases hm with hm | hm
      · exact haR (mem_programAtoms_of_mem_goal (hSR g (by simp)) hm)
      · have hmRest : a ∈ programAtoms rest := by
          simpa [programAtoms] using hm
        exact ih (fun x hx => hSR x (by simp [hx])) hmRest

mutual
  private theorem atomFromAny_cut_core {d : Goal}
      (hDFires : ∀ {P : Program} {a : AtomVar}, Derives P d -> Fires P d a -> Derives P (.atom a)) :
      ∀ {R S : Program} {gs : List Goal} {a : AtomVar},
        (∀ x, x ∈ R ↔ x = d ∨ x ∈ S) ->
        Derives S d ->
        (∀ x, x ∈ gs → x = d ∨ x ∈ S) ->
        DerivesFromAny R gs a ->
        Derives S (.atom a)
    | R, S, head :: tail, a, hRS, hdS, hgs, .here hFire => by
        rcases hgs head (by simp) with rfl | hg
        · exact hDFires hdS (fires_cut_core hDFires hRS hdS hFire)
        · exact derives_atom_of_mem_fires hg (fires_cut_core hDFires hRS hdS hFire)
    | R, S, head :: tail, a, hRS, hdS, hgs, .there hTail => by
        exact atomFromAny_cut_core hDFires hRS hdS
          (fun x hx => hgs x (by simp [hx]))
          hTail

  private theorem derives_cut_core {d : Goal}
      (hDFires : ∀ {P : Program} {a : AtomVar}, Derives P d -> Fires P d a -> Derives P (.atom a)) :
      ∀ {R S : Program} {g : Goal},
        (∀ x, x ∈ R ↔ x = d ∨ x ∈ S) ->
        Derives S d ->
        Derives R g ->
        Derives S g
    | R, S, .atom a, hRS, hdS, .atom hAny => by
        exact atomFromAny_cut_core (d := d) hDFires hRS hdS
          (fun x hx => (hRS x).1 hx)
          hAny
    | R, S, .imp g₁ g₂, hRS, hdS, .imp hSub => by
        have hRS' : ∀ x, x ∈ g₁ :: R ↔ x = d ∨ x ∈ g₁ :: S := by
          intro x
          simp [hRS x, or_left_comm]
        have hdS' : Derives (g₁ :: S) d := derives_weaken (extras := [g₁]) hdS
        exact Derives.imp (derives_cut_core (d := d) hDFires hRS' hdS' hSub)
    | R, S, .conj g₁ g₂, hRS, hdS, .conj h₁ h₂ => by
        exact Derives.conj
          (derives_cut_core (d := d) hDFires hRS hdS h₁)
          (derives_cut_core (d := d) hDFires hRS hdS h₂)
    | R, S, .disj g₁ g₂, hRS, hdS, .disjLeft h => by
        exact Derives.disjLeft (derives_cut_core (d := d) hDFires hRS hdS h)
    | R, S, .disj g₁ g₂, hRS, hdS, .disjRight h => by
        exact Derives.disjRight (derives_cut_core (d := d) hDFires hRS hdS h)
    | R, S, .all g, hRS, hdS, .all a haR haG hSub => by
        have haS : a ∉ programAtoms S :=
          not_mem_programAtoms_of_mono_program
            (fun x hx => (hRS x).2 (Or.inr hx)) haR
        exact Derives.all a haS haG (derives_cut_core (d := d) hDFires hRS hdS hSub)

  private theorem fires_cut_core {d : Goal}
      (hDFires : ∀ {P : Program} {a : AtomVar}, Derives P d -> Fires P d a -> Derives P (.atom a)) :
      ∀ {R S : Program} {g : Goal} {a : AtomVar},
        (∀ x, x ∈ R ↔ x = d ∨ x ∈ S) ->
        Derives S d ->
        Fires R g a ->
        Fires S g a
    | R, S, .atom _, _, hRS, hdS, .atom => by
        exact Fires.atom
    | R, S, .imp g₁ g₂, a, hRS, hdS, .imp hPrem hTail => by
        exact Fires.imp
          (derives_cut_core (d := d) hDFires hRS hdS hPrem)
          (fires_cut_core (d := d) hDFires hRS hdS hTail)
    | R, S, .all g, .atom atm, hRS, hdS, .allAtom _ hSub => by
        exact Fires.allAtom atm (fires_cut_core (d := d) hDFires hRS hdS hSub)
    | R, S, .all g, .bvar k, hRS, hdS, .allBvar c hcR hcG hSub => by
        have hcS : c ∉ programAtoms S :=
          not_mem_programAtoms_of_mono_program
            (fun x hx => (hRS x).2 (Or.inr hx)) hcR
        exact Fires.allBvar c hcS hcG (fires_cut_core (d := d) hDFires hRS hdS hSub)
end

private theorem ambient_cut_core {d : Goal}
    (hDFires : ∀ {P : Program} {a : AtomVar}, Derives P d -> Fires P d a -> Derives P (.atom a)) :
    (∀ {P : Program} {Q : List Goal} {g : Goal},
      Derives P d -> Derives (Q ++ d :: P) g -> Derives (Q ++ P) g) ∧
    (∀ {P : Program} {Q : List Goal} {g : Goal} {a : AtomVar},
      Derives P d -> Fires (Q ++ d :: P) g a -> Fires (Q ++ P) g a) := by
  refine ⟨?_, ?_⟩
  · intro P Q g hd hDer
    have hRS : ∀ x, x ∈ Q ++ d :: P ↔ x = d ∨ x ∈ Q ++ P := by
      intro x
      exact mem_append_cons_cut (Q := Q) (d := d) (P := P) (g := x)
    exact derives_cut_core (d := d) hDFires hRS (derives_weaken (extras := Q) hd) hDer
  · intro P Q g a hd hFire
    have hRS : ∀ x, x ∈ Q ++ d :: P ↔ x = d ∨ x ∈ Q ++ P := by
      intro x
      exact mem_append_cons_cut (Q := Q) (d := d) (P := P) (g := x)
    exact fires_cut_core (d := d) hDFires hRS (derives_weaken (extras := Q) hd) hFire

private theorem cut_package (d : Goal) :
    (∀ {P : Program} {a : AtomVar}, Derives P d -> Fires P d a -> Derives P (.atom a)) ∧
    (∀ {P : Program} {Q : List Goal} {g : Goal},
      Derives P d -> Derives (Q ++ d :: P) g -> Derives (Q ++ P) g) ∧
    (∀ {P : Program} {Q : List Goal} {g : Goal} {a : AtomVar},
      Derives P d -> Fires (Q ++ d :: P) g a -> Fires (Q ++ P) g a) := by
  cases d with
  | atom v =>
      have hDFires : ∀ {P : Program} {a : AtomVar},
          Derives P (.atom v) -> Fires P (.atom v) a -> Derives P (.atom a) := by
        intro P a hd hFire
        cases hFire
        simpa using hd
      have hCut := ambient_cut_core (d := .atom v) hDFires
      exact ⟨hDFires, hCut.1, hCut.2⟩
  | imp g₁ g₂ =>
      have hg₁ := cut_package g₁
      have hg₂ := cut_package g₂
      have hDFires : ∀ {P : Program} {a : AtomVar},
          Derives P (.imp g₁ g₂) -> Fires P (.imp g₁ g₂) a -> Derives P (.atom a) := by
        intro P a hd hFire
        cases hd with
        | imp hSub =>
            cases hFire with
            | imp hPrem hTail =>
                have hG₂ : Derives P g₂ :=
                  hg₁.2.1 (P := P) (Q := []) (g := g₂) hPrem hSub
                exact hg₂.1 hG₂ hTail
      have hCut := ambient_cut_core (d := .imp g₁ g₂) hDFires
      exact ⟨hDFires, hCut.1, hCut.2⟩
  | conj g₁ g₂ =>
      have hDFires : ∀ {P : Program} {a : AtomVar},
          Derives P (.conj g₁ g₂) -> Fires P (.conj g₁ g₂) a -> Derives P (.atom a) := by
        intro P a hd hFire
        cases hFire
      have hCut := ambient_cut_core (d := .conj g₁ g₂) hDFires
      exact ⟨hDFires, hCut.1, hCut.2⟩
  | disj g₁ g₂ =>
      have hDFires : ∀ {P : Program} {a : AtomVar},
          Derives P (.disj g₁ g₂) -> Fires P (.disj g₁ g₂) a -> Derives P (.atom a) := by
        intro P a hd hFire
        cases hFire
      have hCut := ambient_cut_core (d := .disj g₁ g₂) hDFires
      exact ⟨hDFires, hCut.1, hCut.2⟩
  | all g =>
      have hDFires : ∀ {P : Program} {a : AtomVar},
          Derives P (.all g) -> Fires P (.all g) a -> Derives P (.atom a) := by
        intro P a hd hFire
        cases hFire with
        | allAtom atm hSub =>
            exact (cut_package (substGoal g 0 atm)).1 (derives_all_elim atm hd) hSub
        | allBvar c hcP hcG hSub =>
            exact (cut_package (substGoal g 0 c)).1 (derives_all_elim c hd) hSub
      have hCut := ambient_cut_core (d := .all g) hDFires
      exact ⟨hDFires, hCut.1, hCut.2⟩
termination_by goalComplexity d
decreasing_by
  all_goals
    simp [goalComplexity]
    try rw [goalComplexity_substGoal]
    omega

theorem d_fires_derives {P : Program} {d : Goal} {a : AtomVar} :
    Derives P d -> Fires P d a -> Derives P (.atom a) :=
  (cut_package d).1

theorem derives_cut_ambient {P : Program} {Q : List Goal} {d g : Goal} :
    Derives P d -> Derives (Q ++ d :: P) g -> Derives (Q ++ P) g :=
  (cut_package d).2.1

theorem fires_cut_ambient {P : Program} {Q : List Goal} {d g : Goal} {a : AtomVar} :
    Derives P d -> Fires (Q ++ d :: P) g a -> Fires (Q ++ P) g a :=
  (cut_package d).2.2

theorem derives_cut {P : Program} {d g : Goal} :
    Derives P d -> Derives (d :: P) g -> Derives P g := by
  simpa using derives_cut_ambient (P := P) (Q := []) (d := d) (g := g)

theorem derives_of_derived_imp {P : Program} {g₁ g₂ : Goal} :
    Derives P (.imp g₁ g₂) -> Derives P g₁ -> Derives P g₂ := by
  intro hImp hPrem
  cases hImp with
  | imp hBody =>
      exact derives_cut hPrem hBody

theorem search_cut {P : Program} {d g : Goal} :
    SearchSupports P d -> SearchSupports (d :: P) g -> SearchSupports P g := by
  intro hd hg
  exact derives_iff_searchSupports.mp <|
    derives_cut (derives_iff_searchSupports.mpr hd) (derives_iff_searchSupports.mpr hg)

theorem search_of_derived_imp {P : Program} {g₁ g₂ : Goal} :
    SearchSupports P (.imp g₁ g₂) -> SearchSupports P g₁ -> SearchSupports P g₂ := by
  intro hImp hPrem
  exact derives_iff_searchSupports.mp <|
    derives_of_derived_imp
      (derives_iff_searchSupports.mpr hImp)
      (derives_iff_searchSupports.mpr hPrem)

end Contextual
end HeytingLean.PTS.BaseExtension
