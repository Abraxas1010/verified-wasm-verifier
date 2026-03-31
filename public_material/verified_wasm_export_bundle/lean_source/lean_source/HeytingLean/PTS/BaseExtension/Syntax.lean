import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

namespace HeytingLean.PTS.BaseExtension

structure Atom where
  id : Nat
  deriving DecidableEq, Repr, BEq, Hashable

inductive AtomVar where
  | atom : Atom → AtomVar
  | bvar : Nat → AtomVar
  deriving DecidableEq, Repr, BEq

mutual
  inductive Definite where
    | absurd : Definite
    | atom : AtomVar → Definite
    | imp  : Goal → AtomVar → Definite
    | conj : Definite → Definite → Definite
    | all  : Definite → Definite
    deriving DecidableEq, Repr, BEq

  inductive Goal where
    | atom : AtomVar → Goal
    | imp  : Definite → Goal → Goal
    | conj : Goal → Goal → Goal
    | disj : Goal → Goal → Goal
    | all  : Goal → Goal
    deriving DecidableEq, Repr, BEq
end

abbrev Program := List Definite

mutual
  def atomVarAtoms : AtomVar → List Atom
    | .atom a => [a]
    | .bvar _ => []

  def definiteAtoms : Definite → List Atom
    | .absurd => []
    | .atom v => atomVarAtoms v
    | .imp g v => goalAtoms g ++ atomVarAtoms v
    | .conj d₁ d₂ => definiteAtoms d₁ ++ definiteAtoms d₂
    | .all d => definiteAtoms d

  def goalAtoms : Goal → List Atom
    | .atom v => atomVarAtoms v
    | .imp d g => definiteAtoms d ++ goalAtoms g
    | .conj g₁ g₂ => goalAtoms g₁ ++ goalAtoms g₂
    | .disj g₁ g₂ => goalAtoms g₁ ++ goalAtoms g₂
    | .all g => goalAtoms g
end

def programAtoms (P : Program) : List Atom :=
  P.foldr (fun d acc => definiteAtoms d ++ acc) []

def maxAtomId : List Atom → Nat
  | [] => 0
  | a :: atoms => max a.id (maxAtomId atoms)

def freshAtomFromLists (ls : List (List Atom)) : Atom :=
  ⟨maxAtomId (ls.foldr (fun xs acc => xs ++ acc) []) + 1⟩

def freshAtomForGoal (P : Program) (g : Goal) : Atom :=
  ⟨maxAtomId (programAtoms P ++ goalAtoms g) + 1⟩

def freshAtomForAtom (P : Program) (a : Atom) : Atom :=
  ⟨maxAtomId (programAtoms P ++ [a]) + 1⟩

def FreshInProgram (a : Atom) (P : Program) : Prop :=
  a ∉ programAtoms P

def FreshForGoal (a : Atom) (P : Program) (g : Goal) : Prop :=
  a ∉ programAtoms P ∧ a ∉ goalAtoms g

def FreshForAtomGoal (b a : Atom) (P : Program) : Prop :=
  b ≠ a ∧ b ∉ programAtoms P

mutual
  def substAtomVar (n : Nat) (a : Atom) : AtomVar → AtomVar
    | .atom p => .atom p
    | .bvar k => if k = n then .atom a else .bvar k

  def substDefinite (d : Definite) (n : Nat) (a : Atom) : Definite :=
    match d with
    | .absurd => .absurd
    | .atom v => .atom (substAtomVar n a v)
    | .imp g v => .imp (substGoal g n a) (substAtomVar n a v)
    | .conj d₁ d₂ => .conj (substDefinite d₁ n a) (substDefinite d₂ n a)
    | .all d' => .all (substDefinite d' (n + 1) a)

  def substGoal (g : Goal) (n : Nat) (a : Atom) : Goal :=
    match g with
    | .atom v => .atom (substAtomVar n a v)
    | .imp d g' => .imp (substDefinite d n a) (substGoal g' n a)
    | .conj g₁ g₂ => .conj (substGoal g₁ n a) (substGoal g₂ n a)
    | .disj g₁ g₂ => .disj (substGoal g₁ n a) (substGoal g₂ n a)
    | .all g' => .all (substGoal g' (n + 1) a)
end

mutual
  def renameAtomVar (src dst : Atom) : AtomVar → AtomVar
    | .atom a => if a = src then .atom dst else .atom a
    | .bvar n => .bvar n

  def renameDefinite (src dst : Atom) : Definite → Definite
    | .absurd => .absurd
    | .atom v => .atom (renameAtomVar src dst v)
    | .imp g v => .imp (renameGoal src dst g) (renameAtomVar src dst v)
    | .conj d₁ d₂ => .conj (renameDefinite src dst d₁) (renameDefinite src dst d₂)
    | .all d => .all (renameDefinite src dst d)

  def renameGoal (src dst : Atom) : Goal → Goal
    | .atom v => .atom (renameAtomVar src dst v)
    | .imp d g => .imp (renameDefinite src dst d) (renameGoal src dst g)
    | .conj g₁ g₂ => .conj (renameGoal src dst g₁) (renameGoal src dst g₂)
    | .disj g₁ g₂ => .disj (renameGoal src dst g₁) (renameGoal src dst g₂)
    | .all g => .all (renameGoal src dst g)
end

def renameProgram (src dst : Atom) (P : Program) : Program :=
  P.map (renameDefinite src dst)

def clauseClosure : Definite → List Definite
  | .absurd => [.absurd]
  | .conj d₁ d₂ => clauseClosure d₁ ++ clauseClosure d₂
  | d => [d]

def programClosure (P : Program) : List Definite :=
  P.flatMap clauseClosure

mutual
  inductive NeutralDefinite : Definite → Prop where
    | absurd : NeutralDefinite .absurd
    | atom (v : AtomVar) : NeutralDefinite (.atom v)
    | imp  {g : Goal} {v : AtomVar} : NeutralGoal g → NeutralDefinite (.imp g v)
    | conj {d₁ d₂ : Definite} : NeutralDefinite d₁ → NeutralDefinite d₂ → NeutralDefinite (.conj d₁ d₂)
    | all  {d : Definite} : NeutralDefinite d → NeutralDefinite (.all d)

/--
Neutral HH goals exclude disjunction by design: disjunction is the positive goal
former that sits outside the neutral fragment used by the current CPS bridge.
-/
  inductive NeutralGoal : Goal → Prop where
    | atom (v : AtomVar) : NeutralGoal (.atom v)
    | imp  {d : Definite} {g : Goal} : NeutralDefinite d → NeutralGoal g → NeutralGoal (.imp d g)
    | conj {g₁ g₂ : Goal} : NeutralGoal g₁ → NeutralGoal g₂ → NeutralGoal (.conj g₁ g₂)
    | all  {g : Goal} : NeutralGoal g → NeutralGoal (.all g)
end

def InClosure (P : Program) (d : Definite) : Prop :=
  d ∈ programClosure P

def containsDefinite (target : Definite) : List Definite → Bool
  | [] => false
  | d :: ds => if d = target then true else containsDefinite target ds

def inClosureDec (P : Program) (target : Definite) : Bool :=
  containsDefinite target (programClosure P)

end HeytingLean.PTS.BaseExtension
