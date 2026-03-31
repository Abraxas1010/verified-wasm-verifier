import HeytingLean.PTS.BaseExtension.IPL

namespace HeytingLean.PTS.BaseExtension.Contextual

mutual
  inductive Goal where
    | atom : AtomVar → Goal
    | imp : Goal → Goal → Goal
    | conj : Goal → Goal → Goal
    | disj : Goal → Goal → Goal
    | all : Goal → Goal
    deriving DecidableEq, Repr, BEq
end

abbrev Program := List Goal

mutual
  def goalAtoms : Goal → List Atom
    | .atom v => atomVarAtoms v
    | .imp g h => goalAtoms g ++ goalAtoms h
    | .conj g₁ g₂ => goalAtoms g₁ ++ goalAtoms g₂
    | .disj g₁ g₂ => goalAtoms g₁ ++ goalAtoms g₂
    | .all g => goalAtoms g
end

def programAtoms (P : Program) : List Atom :=
  P.foldr (fun g acc => goalAtoms g ++ acc) []

def freshAtomForGoal (P : Program) (g : Goal) : Atom :=
  ⟨maxAtomId (programAtoms P ++ goalAtoms g) + 1⟩

mutual
  def substGoal (g : Goal) (n : Nat) (a : Atom) : Goal :=
    match g with
    | .atom v => .atom (substAtomVar n a v)
    | .imp g₁ g₂ => .imp (substGoal g₁ n a) (substGoal g₂ n a)
    | .conj g₁ g₂ => .conj (substGoal g₁ n a) (substGoal g₂ n a)
    | .disj g₁ g₂ => .disj (substGoal g₁ n a) (substGoal g₂ n a)
    | .all g' => .all (substGoal g' (n + 1) a)
end

mutual
  def search : Nat → Program → Goal → Bool
    | 0, _, _ => false
    | fuel + 1, P, g =>
        match g with
        | .atom a => searchAnyAssumption fuel P P a
        | .imp g₁ g₂ => search fuel (g₁ :: P) g₂
        | .conj g₁ g₂ => search fuel P g₁ && search fuel P g₂
        | .disj g₁ g₂ => search fuel P g₁ || search fuel P g₂
        | .all g' => search fuel P (substGoal g' 0 (freshAtomForGoal P g'))

  def searchAnyAssumption : Nat → Program → List Goal → AtomVar → Bool
    | _, _, [], _ => false
    | fuel, P, g :: rest, a => fires fuel P g a || searchAnyAssumption fuel P rest a

  def fires : Nat → Program → Goal → AtomVar → Bool
    | 0, _, _, _ => false
    | fuel + 1, P, g, a =>
        match g with
        | .atom b => decide (b = a)
        | .imp g₁ g₂ => search fuel P g₁ && fires fuel P g₂ a
        | .conj _ _ => false
        | .disj _ _ => false
        | .all g' =>
            match a with
            | .atom atm => fires fuel P (substGoal g' 0 atm) a
            | .bvar _ => fires fuel P (substGoal g' 0 (freshAtomForGoal P g')) a
end

def SearchSupports (P : Program) (g : Goal) : Prop :=
  ∃ fuel, search fuel P g = true

end Contextual
end HeytingLean.PTS.BaseExtension
