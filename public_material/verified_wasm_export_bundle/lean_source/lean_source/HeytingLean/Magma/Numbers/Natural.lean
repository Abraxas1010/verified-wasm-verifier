import HeytingLean.Magma.Function

namespace HeytingLean.Magma.Numbers

open HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A] [ProductEncoding A]

class NaturalPresentation (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A]
    [PairEncoding A] [ProductEncoding A] where
  baseAtom : A
  mnat_zero : Magma A
  mnat_succ : Magma A → Magma A
  mnat_alt : ℕ → Magma A
  alt_disjoint : ∀ {m n : ℕ}, m ≠ n → Disjoint (Set.singleton (mnat_alt m)) (Set.singleton (mnat_alt n))

variable [NaturalPresentation A]

def mnat_zero : Magma A := NaturalPresentation.mnat_zero (A := A)

def mnat_succ (n : Magma A) : Magma A := NaturalPresentation.mnat_succ (A := A) n

def mnat_alt (n : ℕ) : Magma A := NaturalPresentation.mnat_alt (A := A) n

theorem mnat_alt_disjoint (m n : ℕ) (h : m ≠ n) :
    Disjoint (Set.singleton (mnat_alt (A := A) m)) (Set.singleton (mnat_alt (A := A) n)) :=
  NaturalPresentation.alt_disjoint h

end HeytingLean.Magma.Numbers
