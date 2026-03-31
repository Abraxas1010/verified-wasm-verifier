import Mathlib.Data.List.Basic
import HeytingLean.PTS.BaseExtension.Syntax

namespace HeytingLean.PTS.BaseExtension

inductive IPL where
  | atom : Atom → IPL
  | bot : IPL
  | conj : IPL → IPL → IPL
  | disj : IPL → IPL → IPL
  | imp : IPL → IPL → IPL
  deriving DecidableEq, Repr, BEq

def IPL.atoms : IPL → List Atom
  | .atom a => [a]
  | .bot => []
  | .conj φ ψ => φ.atoms ++ ψ.atoms
  | .disj φ ψ => φ.atoms ++ ψ.atoms
  | .imp φ ψ => φ.atoms ++ ψ.atoms

def IPL.atomCount : IPL → Nat
  | .atom _ => 1
  | .bot => 0
  | .conj φ ψ => φ.atomCount + ψ.atomCount
  | .disj φ ψ => φ.atomCount + ψ.atomCount
  | .imp φ ψ => φ.atomCount + ψ.atomCount

def extends_ (B B' : Program) : Prop :=
  ∀ d, d ∈ B → d ∈ B'

theorem extends_refl (B : Program) : extends_ B B := by
  intro d hd
  exact hd

theorem extends_cons (B : Program) (d : Definite) : extends_ B (d :: B) := by
  intro d' hd'
  exact List.mem_cons_of_mem _ hd'

def peirceFormula (p q : Atom) : IPL :=
  .imp (.imp (.imp (.atom p) (.atom q)) (.atom p)) (.atom p)

def identityFormula (p : Atom) : IPL :=
  .imp (.atom p) (.atom p)

def modusPonensConclusion (q : Atom) : IPL :=
  .atom q

end HeytingLean.PTS.BaseExtension
