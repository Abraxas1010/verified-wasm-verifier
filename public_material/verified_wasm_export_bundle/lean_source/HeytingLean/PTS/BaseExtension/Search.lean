import Mathlib.Data.List.Basic
import HeytingLean.PTS.BaseExtension.Operational

namespace HeytingLean.PTS.BaseExtension

def impWitnessesFromList (ds : List Definite) (a : AtomVar) : List Goal :=
  ds.filterMap fun d =>
    match d with
    | .imp g a' => if a' = a then some g else none
    | _ => none

def allWitnessBodiesFromList (ds : List Definite) : List Definite :=
  ds.filterMap fun d =>
    match d with
    | .all body => some body
    | _ => none

def impWitnesses (P : Program) (a : AtomVar) : List Goal :=
  impWitnessesFromList (programClosure P) a

def allWitnessBodies (P : Program) : List Definite :=
  allWitnessBodiesFromList (programClosure P)

def absurdSearch (P : Program) : Bool :=
  inClosureDec P .absurd

def factSearch (P : Program) (a : AtomVar) : Bool :=
  inClosureDec P (.atom a)

mutual
  def search : Nat → Program → Goal → Bool
    | 0, _, _ => false
    | fuel + 1, P, g =>
        match g with
        | .atom a =>
            absurdSearch P ||
              factSearch P a ||
              searchGoals fuel P (impWitnesses P a) ||
              match a with
              | .atom atm => searchInstances fuel P atm (allWitnessBodies P)
              | .bvar _ => false
        | .conj g₁ g₂ => search fuel P g₁ && search fuel P g₂
        | .disj g₁ g₂ => search fuel P g₁ || search fuel P g₂
        | .imp d g' => search fuel (d :: P) g'
        | .all g' => search fuel P (substGoal g' 0 (freshAtomForGoal P g'))

  def searchGoals : Nat → Program → List Goal → Bool
    | _, _, [] => false
    | fuel, P, g' :: rest => search fuel P g' || searchGoals fuel P rest

  def searchInstances (fuel : Nat) (P : Program) (a : Atom) : List Definite → Bool
    | [] => false
    | body :: rest =>
        search fuel (substDefinite body 0 (freshAtomForAtom P a) :: P) (.atom (.atom a)) ||
          searchInstances fuel P a rest
end

def SearchSupports (P : Program) (g : Goal) : Prop :=
  ∃ fuel, search fuel P g = true

inductive SearchDerives : Nat → Program → Goal → Prop where
  | absurd {fuel : Nat} {P : Program} {a : AtomVar} :
      InClosure P .absurd →
      SearchDerives (fuel + 1) P (.atom a)
  | fact {fuel : Nat} {P : Program} {a : AtomVar} :
      InClosure P (.atom a) →
      SearchDerives (fuel + 1) P (.atom a)
  | backchain {fuel : Nat} {P : Program} {g : Goal} {a : AtomVar} :
      InClosure P (.imp g a) →
      SearchDerives fuel P g →
      SearchDerives (fuel + 1) P (.atom a)
  | instance_ {fuel : Nat} {P : Program} {d : Definite} {a : Atom} :
      InClosure P (.all d) →
      SearchDerives fuel (substDefinite d 0 (freshAtomForAtom P a) :: P) (.atom (.atom a)) →
      SearchDerives (fuel + 1) P (.atom (.atom a))
  | andI {fuel : Nat} {P : Program} {g₁ g₂ : Goal} :
      SearchDerives fuel P g₁ →
      SearchDerives fuel P g₂ →
      SearchDerives (fuel + 1) P (.conj g₁ g₂)
  | orL {fuel : Nat} {P : Program} {g₁ g₂ : Goal} :
      SearchDerives fuel P g₁ →
      SearchDerives (fuel + 1) P (.disj g₁ g₂)
  | orR {fuel : Nat} {P : Program} {g₁ g₂ : Goal} :
      SearchDerives fuel P g₂ →
      SearchDerives (fuel + 1) P (.disj g₁ g₂)
  | augment {fuel : Nat} {P : Program} {d : Definite} {g : Goal} :
      SearchDerives fuel (d :: P) g →
      SearchDerives (fuel + 1) P (.imp d g)
  | generic {fuel : Nat} {P : Program} {g : Goal} :
      SearchDerives fuel P (substGoal g 0 (freshAtomForGoal P g)) →
      SearchDerives (fuel + 1) P (.all g)

lemma factSearch_true_iff {P : Program} {a : AtomVar} :
    factSearch P a = true ↔ InClosure P (.atom a) := by
  let target : Definite := .atom a
  have hmem : ∀ ds : List Definite, containsDefinite target ds = true ↔ target ∈ ds := by
    intro ds
    induction ds with
    | nil =>
        simp [containsDefinite]
    | cons d ds ih =>
        by_cases hEq : d = target
        · simp [containsDefinite, hEq]
        · simp [containsDefinite, hEq, ih]
          intro hEq'
          exact (hEq hEq'.symm).elim
  unfold factSearch inClosureDec InClosure
  simpa [target] using hmem (programClosure P)

lemma absurdSearch_true_iff {P : Program} :
    absurdSearch P = true ↔ InClosure P .absurd := by
  let target : Definite := .absurd
  have hmem : ∀ ds : List Definite, containsDefinite target ds = true ↔ target ∈ ds := by
    intro ds
    induction ds with
    | nil =>
        simp [containsDefinite]
    | cons d ds ih =>
        by_cases hEq : d = target
        · simp [containsDefinite, hEq]
        · simp [containsDefinite, hEq, ih]
          intro hEq'
          exact (hEq hEq'.symm).elim
  unfold absurdSearch inClosureDec InClosure
  simpa [target] using hmem (programClosure P)

lemma mem_impWitnessesFromList_iff {ds : List Definite} {g : Goal} {a : AtomVar} :
    g ∈ impWitnessesFromList ds a ↔ (.imp g a) ∈ ds := by
  rw [impWitnessesFromList, List.mem_filterMap]
  constructor
  · rintro ⟨d, hd, hs⟩
    cases d <;> simp at hs hd ⊢
    case imp g' a' =>
      rcases hs with ⟨rfl, hEq⟩
      simpa [hEq] using hd
  · intro h
    exact ⟨.imp g a, h, by simp⟩

lemma mem_allWitnessBodiesFromList_iff {ds : List Definite} {body : Definite} :
    body ∈ allWitnessBodiesFromList ds ↔ (.all body) ∈ ds := by
  rw [allWitnessBodiesFromList, List.mem_filterMap]
  constructor
  · rintro ⟨d, hd, hs⟩
    cases d <;> simp at hs hd ⊢
    case all body' =>
      rcases hs with rfl
      simpa using hd
  · intro h
    exact ⟨.all body, h, by simp⟩

lemma mem_impWitnesses_iff {P : Program} {g : Goal} {a : AtomVar} :
    g ∈ impWitnesses P a ↔ InClosure P (.imp g a) := by
  unfold impWitnesses InClosure
  simp [mem_impWitnessesFromList_iff]

lemma mem_allWitnessBodies_iff {P : Program} {body : Definite} :
    body ∈ allWitnessBodies P ↔ InClosure P (.all body) := by
  unfold allWitnessBodies InClosure
  simp [mem_allWitnessBodiesFromList_iff]

lemma searchGoals_sound {fuel : Nat} {P : Program} {gs : List Goal} :
    searchGoals fuel P gs = true →
      ∃ g, g ∈ gs ∧ search fuel P g = true := by
  induction gs with
  | nil =>
      simp [searchGoals]
  | cons g gs ih =>
      intro h
      have h' : search fuel P g = true ∨ searchGoals fuel P gs = true := by
        simpa [searchGoals] using h
      rcases h' with h0 | hrest
      · exact ⟨g, by simp, h0⟩
      · rcases ih hrest with ⟨g', hg', hs⟩
        exact ⟨g', by simp [hg'], hs⟩

lemma searchGoals_complete {fuel : Nat} {P : Program} {gs : List Goal} :
    (∃ g, g ∈ gs ∧ search fuel P g = true) → searchGoals fuel P gs = true := by
  induction gs with
  | nil =>
      intro h
      rcases h with ⟨_, hmem, _⟩
      cases hmem
  | cons g gs ih =>
      intro h
      rcases h with ⟨g', hg', hs⟩
      simp at hg'
      rcases hg' with rfl | htail
      · simp [searchGoals, hs]
      · simp [searchGoals, ih ⟨g', htail, hs⟩]

lemma searchInstances_sound {fuel : Nat} {P : Program} {a : Atom} {ds : List Definite} :
    searchInstances fuel P a ds = true →
      ∃ d, d ∈ ds ∧
        search fuel (substDefinite d 0 (freshAtomForAtom P a) :: P) (.atom (.atom a)) = true := by
  induction ds with
  | nil =>
      simp [searchInstances]
  | cons d ds ih =>
      intro h
      have h' :
          search fuel (substDefinite d 0 (freshAtomForAtom P a) :: P) (.atom (.atom a)) = true ∨
            searchInstances fuel P a ds = true := by
        simpa [searchInstances] using h
      rcases h' with h0 | hrest
      · exact ⟨d, by simp, h0⟩
      · rcases ih hrest with ⟨d', hd', hs⟩
        exact ⟨d', by simp [hd'], hs⟩

lemma searchInstances_complete {fuel : Nat} {P : Program} {a : Atom} {ds : List Definite} :
    (∃ d, d ∈ ds ∧
      search fuel (substDefinite d 0 (freshAtomForAtom P a) :: P) (.atom (.atom a)) = true) →
    searchInstances fuel P a ds = true := by
  induction ds with
  | nil =>
      intro h
      rcases h with ⟨_, hmem, _⟩
      cases hmem
  | cons d ds ih =>
      intro h
      rcases h with ⟨d', hd', hs⟩
      simp at hd'
      rcases hd' with rfl | htail
      · simp [searchInstances, hs]
      · simp [searchInstances, ih ⟨d', htail, hs⟩]

lemma SearchDerives.toProves {fuel : Nat} {P : Program} {g : Goal} :
    SearchDerives fuel P g → Proves P g := by
  intro h
  induction h with
  | absurd hAbs =>
      exact Proves.absurd hAbs
  | fact hFact =>
      exact Proves.fact hFact
  | backchain hImp _ ih =>
      exact Proves.backchain hImp ih
  | instance_ hAll _ ih =>
      exact Proves.instance_ hAll ih
  | andI _ _ ih₁ ih₂ =>
      exact Proves.andI ih₁ ih₂
  | orL _ ih =>
      exact Proves.orL ih
  | orR _ ih =>
      exact Proves.orR ih
  | augment _ ih =>
      exact Proves.augment ih
  | generic _ ih =>
      exact Proves.generic ih

def SearchDerives.lift {fuel : Nat} {P : Program} {g : Goal} :
    SearchDerives fuel P g → SearchDerives (fuel + 1) P g
  | .absurd (fuel := n) hAbs =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (SearchDerives.absurd (fuel := n + 1) hAbs)
  | .fact (fuel := n) hFact =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (SearchDerives.fact (fuel := n + 1) hFact)
  | .backchain (fuel := n) hImp hDer =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (SearchDerives.backchain (fuel := n + 1) hImp (SearchDerives.lift hDer))
  | .instance_ (fuel := n) hAll hDer =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (SearchDerives.instance_ (fuel := n + 1) hAll (SearchDerives.lift hDer))
  | .andI (fuel := n) h₁ h₂ =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (SearchDerives.andI (fuel := n + 1) (SearchDerives.lift h₁) (SearchDerives.lift h₂))
  | .orL (fuel := n) h =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (SearchDerives.orL (fuel := n + 1) (SearchDerives.lift h))
  | .orR (fuel := n) h =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (SearchDerives.orR (fuel := n + 1) (SearchDerives.lift h))
  | .augment (fuel := n) h =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (SearchDerives.augment (fuel := n + 1) (SearchDerives.lift h))
  | .generic (fuel := n) h =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (SearchDerives.generic (fuel := n + 1) (SearchDerives.lift h))

lemma SearchDerives.monotone {fuel : Nat} {P : Program} {g : Goal} :
    SearchDerives fuel P g → ∀ extra : Nat, SearchDerives (fuel + extra) P g := by
  intro h extra
  induction extra with
  | zero =>
      simpa using h
  | succ extra ih =>
      simpa [Nat.add_assoc] using (SearchDerives.lift ih)

def SearchDerives.toBool {fuel : Nat} {P : Program} {g : Goal} :
    SearchDerives fuel P g → search fuel P g = true
  | .absurd (fuel := fuel) (a := a) hAbs =>
      by
        have hA : absurdSearch P = true := absurdSearch_true_iff.mpr hAbs
        cases a <;> simp [search, hA]
  | .fact (fuel := fuel) (a := a) hFact =>
      by
        have hf : factSearch P a = true := factSearch_true_iff.mpr hFact
        cases a <;> simp [search, hf]
  | .backchain (fuel := fuel) (g := g) (a := a) hImp hDer =>
      by
        have hs : searchGoals fuel P (impWitnesses P a) = true :=
          searchGoals_complete ⟨_, mem_impWitnesses_iff.mpr hImp, hDer.toBool⟩
        cases a <;> simp [search, hs]
  | .instance_ (fuel := fuel) (a := a) hAll hDer =>
      by
        have hs := searchInstances_complete ⟨_, mem_allWitnessBodies_iff.mpr hAll, hDer.toBool⟩
        simp [search, hs]
  | .andI h₁ h₂ =>
      by simp [search, h₁.toBool, h₂.toBool]
  | .orL h =>
      by simp [search, h.toBool]
  | .orR h =>
      by simp [search, h.toBool]
  | .augment h =>
      by simpa [search] using h.toBool
  | .generic h =>
      by simpa [search] using h.toBool

lemma search_derives_of_true {fuel : Nat} {P : Program} {g : Goal} :
    search fuel P g = true → SearchDerives fuel P g := by
  induction fuel generalizing P g with
  | zero =>
      simp [search]
  | succ fuel ih =>
      cases g with
      | atom a =>
          intro h
          cases a with
          | atom atm =>
              have h' :
                  ((absurdSearch P = true ∨ factSearch P (.atom atm) = true) ∨
                    searchGoals fuel P (impWitnesses P (.atom atm)) = true) ∨
                    searchInstances fuel P atm (allWitnessBodies P) = true := by
                simpa [search] using h
              rcases h' with hLeft | hInst
              · rcases hLeft with hFact | hBack
                · rcases hFact with hAbs | hFact
                  · exact SearchDerives.absurd (fuel := fuel) (absurdSearch_true_iff.mp hAbs)
                  · exact SearchDerives.fact (fuel := fuel) (factSearch_true_iff.mp hFact)
                · rcases searchGoals_sound hBack with ⟨g', hg', hs⟩
                  exact SearchDerives.backchain
                    (mem_impWitnesses_iff.mp hg')
                    (ih hs)
              · rcases searchInstances_sound hInst with ⟨d, hd, hs⟩
                exact SearchDerives.instance_
                  (mem_allWitnessBodies_iff.mp hd)
                  (ih hs)
          | bvar n =>
              have h' :
                  (absurdSearch P = true ∨ factSearch P (.bvar n) = true) ∨
                    searchGoals fuel P (impWitnesses P (.bvar n)) = true := by
                simpa [search] using h
              rcases h' with hFact | hBack
              · rcases hFact with hAbs | hFact
                · exact SearchDerives.absurd (fuel := fuel) (absurdSearch_true_iff.mp hAbs)
                · exact SearchDerives.fact (fuel := fuel) (factSearch_true_iff.mp hFact)
              · rcases searchGoals_sound hBack with ⟨g', hg', hs⟩
                exact SearchDerives.backchain
                  (mem_impWitnesses_iff.mp hg')
                  (ih hs)
      | conj g₁ g₂ =>
          intro h
          have h' : search fuel P g₁ = true ∧ search fuel P g₂ = true := by
            simpa [search] using h
          exact SearchDerives.andI (ih h'.1) (ih h'.2)
      | disj g₁ g₂ =>
          simp [search]
          intro h
          rcases h with h | h
          · exact SearchDerives.orL (ih h)
          · exact SearchDerives.orR (ih h)
      | imp d g' =>
          simp [search]
          intro h
          exact SearchDerives.augment (ih h)
      | all g' =>
          simp [search]
          intro h
          exact SearchDerives.generic (ih h)

@[simp] theorem searchGoals_nil (fuel : Nat) (P : Program) :
    searchGoals fuel P [] = false := by
  simp [searchGoals]

@[simp] theorem searchInstances_nil (fuel : Nat) (P : Program) (a : Atom) :
    searchInstances fuel P a [] = false := by
  simp [searchInstances]

def modusPonensProgram (p q : Atom) : Program :=
  [
    .atom (.atom p),
    .imp (.atom (.atom p)) (AtomVar.atom q)
  ]

def peirceGoal (p q : Atom) : Goal :=
  let pq : Definite := .imp (.atom (.atom p)) (AtomVar.atom q)
  let peirceHead : Definite := .imp (.imp pq (.atom (.atom p))) (AtomVar.atom p)
  .imp peirceHead (.atom (.atom p))

def idGoal (p : Atom) : Goal :=
  .imp (.atom (.atom p)) (.atom (.atom p))

example : search 4 (modusPonensProgram ⟨0⟩ ⟨1⟩) (.atom (.atom ⟨1⟩)) = true := by
  native_decide

example : search 3 [] (idGoal ⟨0⟩) = true := by
  native_decide

example : search 5 [] (peirceGoal ⟨0⟩ ⟨1⟩) = false := by
  native_decide

end HeytingLean.PTS.BaseExtension
