import Mathlib.Data.Fin.Basic

/-!
# Pointed finite sets `Fin₀ n`

For CuTe layout categories it is convenient to model the pointed finite set
`{*,0,1,...,n-1}` as `Option (Fin n)`, where `none` is the basepoint `*`.
-/

namespace HeytingLean
namespace Layouts
namespace Tuple

/-- Pointed `Fin`: `none` is the basepoint. -/
abbrev Fin0 (n : ℕ) : Type := Option (Fin n)

namespace Fin0

def base {n : ℕ} : Fin0 n := none

def ofFin {n : ℕ} (i : Fin n) : Fin0 n := some i

end Fin0

/-- Pointed maps `Fin₀ m → Fin₀ n` (must preserve the basepoint). -/
structure Fin0Hom (m n : ℕ) where
  toFun : Fin0 m → Fin0 n
  map_base : toFun none = none

namespace Fin0Hom

instance {m n : ℕ} : CoeFun (Fin0Hom m n) (fun _ => Fin0 m → Fin0 n) :=
  ⟨Fin0Hom.toFun⟩

@[ext] theorem ext {m n : ℕ} {f g : Fin0Hom m n} (h : f.toFun = g.toFun) : f = g := by
  cases f with
  | mk fFun fBase =>
    cases g with
    | mk gFun gBase =>
      cases h
      have : fBase = gBase := by
        apply Subsingleton.elim
      cases this
      rfl

def id (n : ℕ) : Fin0Hom n n :=
  ⟨fun x => x, rfl⟩

def comp {l m n : ℕ} (g : Fin0Hom m n) (f : Fin0Hom l m) : Fin0Hom l n :=
  ⟨g.toFun ∘ f.toFun, by simp [Function.comp, g.map_base, f.map_base]⟩

@[simp] theorem id_toFun (n : ℕ) : (id n).toFun = (fun x => x) := rfl

@[simp] theorem comp_apply {l m n : ℕ} (g : Fin0Hom m n) (f : Fin0Hom l m) (x : Fin0 l) :
    (comp g f) x = g (f x) := rfl

end Fin0Hom

end Tuple
end Layouts
end HeytingLean
