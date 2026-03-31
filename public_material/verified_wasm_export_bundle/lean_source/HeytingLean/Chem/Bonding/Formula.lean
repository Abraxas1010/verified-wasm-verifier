import HeytingLean.Chem.PeriodicTable.CIAAW2024
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace HeytingLean.Chem

open HeytingLean.Chem.PeriodicTable

-- A stoichiometric formula as element -> multiplicity.
--
-- Note: `Element` is finite (`Fin 118`), so we can compute a "sparse view" (support/terms)
-- without storing a separate sparse map structure.
abbrev Formula : Type := Element -> Nat

namespace Formula

def count (f : Formula) (e : Element) : Nat := f e

instance : Zero Formula := ⟨fun _ => 0⟩

def add (f g : Formula) : Formula := fun e => f e + g e

instance : HAdd Formula Formula Formula := ⟨add⟩

def smul (n : Nat) (f : Formula) : Formula := fun e => n * f e

instance : SMul Nat Formula := ⟨smul⟩

def single (e : Element) (n : Nat) : Formula :=
  fun e' => if e' = e then n else 0

-- Finite support (elements with nonzero multiplicity).
def support (f : Formula) : Finset Element :=
  Finset.filter (fun e : Element => f e ≠ 0) Fintype.elems

-- Sparse term set view, suitable for iteration/folds (e.g. reaction balancing).
def termSet (f : Formula) : Finset (Element × Nat) :=
  (support f).image (fun e => (e, f e))

@[simp] theorem add_apply (f g : Formula) (e : Element) : (f + g) e = f e + g e := rfl
@[simp] theorem smul_apply (n : Nat) (f : Formula) (e : Element) : (n • f) e = n * f e := rfl
@[simp] theorem zero_apply (e : Element) : (0 : Formula) e = 0 := rfl
@[simp] theorem single_apply (e e' : Element) (n : Nat) :
    single e n e' = (if e' = e then n else 0) := rfl
@[simp] theorem count_apply (f : Formula) (e : Element) : count f e = f e := rfl

end Formula

end HeytingLean.Chem
