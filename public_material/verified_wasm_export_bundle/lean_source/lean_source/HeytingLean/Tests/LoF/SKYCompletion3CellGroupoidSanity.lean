import HeytingLean.LoF.Combinators.Category.Completion3CellGroupoid
import HeytingLean.LoF.Combinators.Category.CompletionTricategoryThin

/-!
# Smoke test: thin groupoid packaging of `Completion3Cell`

This file checks that for fixed boundaries `p q : a ⟶ b`,
the type `Completion2Path p q` carries a `Groupoid` structure where
morphisms are existence of explicit `Completion3Cell` witnesses.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF.Combinators.Category

example {a b : MWObj} (p q : a ⟶ b) : Groupoid (Completion2Path p q) := by
  infer_instance

#check skyCompletionThinTricategory

example {a b : MWObj} {p q : a ⟶ b} (η : Completion2Path p q) : η ⟶ η := by
  exact 𝟙 η

example {a b : MWObj} {p q : a ⟶ b} {η η' : Completion2Path p q} (h : Completion3Cell η η') :
    η ⟶ η' :=
  Completion3Cell.Exists3Cell.ofCell h

end LoF
end Tests
end HeytingLean
