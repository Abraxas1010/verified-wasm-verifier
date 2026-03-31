import HeytingLean.LoF.HoTT.Identity

/-
An optional path-style identity type for HoTT-flavoured reasoning.

This module introduces an inductive `Path` type living in `Sort` so
that higher-structure (groupoid laws, J-rule) can be expressed
without changing the core `Id` alias, which remains definitionally
equal to propositional equality.  Nothing in the main LoF library
depends on `Path`; it is an additive layer for future HoTT-style
extensions.
-/

namespace HeytingLean
namespace LoF
namespace HoTT

universe u v

/-- Path-style identity type (HoTT-style), living in a universe one
level higher than its carrier so that it never collapses to `Prop`. -/
inductive Path {α : Sort u} (x : α) : α → Sort (u + 1) where
  | refl : Path x x

notation:50 x " ≡ " y => Path x y

namespace Path

/-- Symmetry of path equality. -/
def symm {α : Sort u} {x y : α} :
    Path x y → Path y x
  | .refl => .refl

/-- Transitivity of path equality. -/
def trans {α : Sort u} {x y z : α} :
    Path x y → Path y z → Path x z
  | .refl, p₂ => p₂

/-- Congruence of paths under a function. -/
def cong {α : Sort u} {β : Sort v} (f : α → β)
    {x y : α} :
    Path x y → Path (f x) (f y)
  | .refl => .refl

/-- J-rule / path induction for `Path`. -/
def elim {α : Sort u} {x : α}
    {P : ∀ {y : α}, Path x y → Sort v}
    (h : P (y := x) (.refl)) :
    ∀ {y : α} (p : Path x y), P p
  | _, .refl => h

end Path

/-- Specialisation of `Path` to LoF propositions/forms. -/
abbrev FormPath {Form : Sort u} (P Q : Form) : Sort (u + 1) :=
  Path P Q

notation:50 P " ≃ₚₚ " Q => FormPath P Q

end HoTT
end LoF
end HeytingLean
