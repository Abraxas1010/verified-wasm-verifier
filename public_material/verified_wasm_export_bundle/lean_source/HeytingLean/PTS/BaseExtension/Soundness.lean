import HeytingLean.PTS.BaseExtension.Encoding
import HeytingLean.PTS.BaseExtension.Support

namespace HeytingLean.PTS.BaseExtension

lemma programClosure_encodeBase (B : Base) :
    programClosure (encodeBase B) = encodeBase B := by
  induction B with
  | nil =>
      simp [programClosure, encodeBase]
  | cons hd tl ih =>
      simpa [programClosure, encodeBase, clauseClosure] using congrArg (List.cons (Definite.atom (.atom hd))) ih

lemma impWitnesses_encodeBase (B : Base) (a : AtomVar) :
    impWitnesses (encodeBase B) a = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro g hg
  unfold impWitnesses at hg
  rw [programClosure_encodeBase] at hg
  have hImp : Definite.imp g a ∈ encodeBase B := (mem_impWitnessesFromList_iff).1 hg
  simp [encodeBase] at hImp

lemma allWitnessBodies_encodeBase (B : Base) :
    allWitnessBodies (encodeBase B) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro body hbody
  unfold allWitnessBodies at hbody
  rw [programClosure_encodeBase] at hbody
  have hAll : Definite.all body ∈ encodeBase B := (mem_allWitnessBodiesFromList_iff).1 hbody
  simp [encodeBase] at hAll

lemma containsDefinite_eq_true_iff_mem (target : Definite) (ds : List Definite) :
    containsDefinite target ds = true ↔ target ∈ ds := by
  induction ds with
  | nil =>
      simp [containsDefinite]
  | cons d ds ih =>
      by_cases h : d = target
      · simp [containsDefinite, h]
      · constructor
        · intro hContains
          simp [containsDefinite, h] at hContains
          exact List.mem_cons_of_mem _ (ih.1 hContains)
        · intro hMem
          rcases List.mem_cons.mp hMem with hHead | hTail
          · exact False.elim (h hHead.symm)
          · simp [containsDefinite, h, ih.2 hTail]

lemma factSearch_encodeBase_atom_iff {B : Base} {a : Atom} :
    factSearch (encodeBase B) (.atom a) = true ↔ a ∈ B := by
  unfold factSearch inClosureDec
  rw [programClosure_encodeBase]
  have habsurd : containsDefinite .absurd (encodeBase B) = false := by
    cases h : containsDefinite .absurd (encodeBase B) with
    | false =>
        rfl
    | true =>
        have : .absurd ∈ encodeBase B := (containsDefinite_eq_true_iff_mem .absurd (encodeBase B)).1 h
        simp [encodeBase] at this
  have hatom : containsDefinite (.atom (.atom a)) (encodeBase B) = true ↔ a ∈ B := by
    exact (containsDefinite_eq_true_iff_mem (.atom (.atom a)) (encodeBase B)).trans encodeBase_mem
  simpa [habsurd, Bool.or_eq_true] using hatom

lemma factSearch_encodeBase_atom_false_of_not_mem {B : Base} {a : Atom} (ha : a ∉ B) :
    factSearch (encodeBase B) (.atom a) = false := by
  cases hfact : factSearch (encodeBase B) (.atom a) with
  | false =>
      rfl
  | true =>
      exact False.elim (ha ((factSearch_encodeBase_atom_iff).1 hfact))

lemma search_encodeBase_atom_eq_factSearch (fuel : Nat) (B : Base) (a : Atom) :
    search (fuel + 1) (encodeBase B) (encode (.atom a)) = factSearch (encodeBase B) (.atom a) := by
  have habsurd : absurdSearch (encodeBase B) = false := by
    unfold absurdSearch inClosureDec
    rw [programClosure_encodeBase]
    cases h : containsDefinite Definite.absurd (encodeBase B) with
    | false =>
        rfl
    | true =>
        have : Definite.absurd ∈ encodeBase B :=
          (containsDefinite_eq_true_iff_mem Definite.absurd (encodeBase B)).1 h
        simp [encodeBase] at this
  simp [encode, search, impWitnesses_encodeBase, allWitnessBodies_encodeBase, habsurd]

lemma search_encodeBase_atom_false_of_not_mem (fuel : Nat) (B : Base) (a : Atom) (ha : a ∉ B) :
    search fuel (encodeBase B) (encode (.atom a)) = false := by
  cases fuel with
  | zero =>
      simp [search]
  | succ fuel =>
      rw [search_encodeBase_atom_eq_factSearch fuel B a]
      exact factSearch_encodeBase_atom_false_of_not_mem ha

lemma search_encodeBase_bot_false (fuel : Nat) (B : Base) :
    search fuel (encodeBase B) (encode .bot) = false := by
  cases fuel with
  | zero =>
      simp [search, encode]
  | succ fuel =>
      let fresh := freshAtomForGoal (encodeBase B) (Goal.atom (AtomVar.bvar 0))
      have hfreshProg : fresh ∉ programAtoms (encodeBase B) :=
        (freshAtomForGoal_fresh (encodeBase B) (Goal.atom (AtomVar.bvar 0))).1
      have hfreshBase : fresh ∉ B := by
        simpa [programAtoms_encodeBase] using hfreshProg
      simpa [encode, search, fresh] using search_encodeBase_atom_false_of_not_mem fuel B fresh hfreshBase

theorem atom_support_implies_search (B : Base) (a : Atom) :
    Supports B (.atom a) → SearchSupports (encodeBase B) (encode (.atom a)) := by
  intro h
  refine ⟨1, ?_⟩
  have hfact : factSearch (encodeBase B) (.atom a) = true :=
    (factSearch_encodeBase_atom_iff).2 h
  rw [search_encodeBase_atom_eq_factSearch 0 B a]
  exact hfact

theorem bot_support_implies_search (B : Base) :
    Supports B .bot → SearchSupports (encodeBase B) (encode .bot) := by
  intro h
  exact False.elim h

lemma search_imp_atom_atom_eq_search_cons (fuel : Nat) (B : Base) (p q : Atom) :
    search (fuel + 1) (encodeBase B) (encode (.imp (.atom p) (.atom q))) =
      search fuel (encodeBase (p :: B)) (encode (.atom q)) := by
  simp [encode, encodeD, search, encodeBase]

theorem atomImp_support_implies_search (B : Base) (p q : Atom) :
    Supports B (.imp (.atom p) (.atom q)) →
      SearchSupports (encodeBase B) (encode (.imp (.atom p) (.atom q))) := by
  intro h
  have hcons : Supports (p :: B) (.atom q) := by
    rcases (supports_atom_imp_atom_iff B p q).1 h with rfl | hq
    · simp [Supports]
    · simp [Supports, hq]
  rcases atom_support_implies_search (p :: B) q hcons with ⟨fuel, hfuel⟩
  refine ⟨fuel + 1, ?_⟩
  rw [search_imp_atom_atom_eq_search_cons]
  exact hfuel

theorem search_sound {fuel : Nat} {P : Program} {g : Goal} :
    search fuel P g = true → Proves P g := by
  intro h
  exact (search_derives_of_true h).toProves

end HeytingLean.PTS.BaseExtension
