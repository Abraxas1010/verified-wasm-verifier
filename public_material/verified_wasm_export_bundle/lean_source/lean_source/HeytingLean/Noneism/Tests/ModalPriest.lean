import HeytingLean.Noneism.Semantics.ModalPriest

namespace HeytingLean
namespace Noneism
namespace Tests

open ModalPriest
open Noneism Formula

namespace MPEx

inductive Atom where | Detective deriving DecidableEq, Repr, Inhabited

-- Two worlds: α and one possible world p1
inductive W | alpha | p1 deriving DecidableEq, Repr, Inhabited

def kind : W → Kind
  | .alpha => .α
  | .p1    => .P

def D := Unit
def holmes : D := ()

def interp : W → Atom → (List D → Prop)
  | .alpha, .Detective => fun _ => False
  | .p1,    .Detective => fun _ => True

def existsP : W → D → Prop := fun _ _ => True
def about   : W → D → Prop := fun w _ => w = W.alpha

def realize : (D → Prop) → (W → Prop) := fun _ w => w = W.p1
def item    : (D → Prop) → D := fun _ => holmes

def M : Model Atom D :=
  { W := W, kind := kind, α := W.alpha
  , interp := interp, existsP := existsP
  , about := about, realize := realize, item := item
  } -- only p1 realizes χ; item choice irrelevant

end MPEx

open MPEx

/-- In the `MPEx` example, the trivial characterization `χ := True` is realized at `p1`. -/
theorem cp_holds_on_realization :
    M.realize (fun (_ : D) => True) W.p1 := by
  -- By construction, `realize χ` holds exactly at `p1` for all χ.
  simp [M, MPEx.realize]

/-- Aboutness at α holds for the created item in this example. -/
theorem aboutness_true_at_alpha : M.about M.α (item (fun (_ : D) => True)) := by
  simp [M, MPEx.about]

/-- Satisfaction aligns with the world-indexed interpretation. -/
def ρ : Valuation D := fun _ => ()

def Detective : Formula Atom := .pred .Detective []

theorem detective_true_at_p1 : eval M ρ W.p1 Detective := by
  simp [eval, Detective, M, interp]

theorem detective_false_at_alpha : ¬ eval M ρ W.alpha Detective := by
  simp [eval, Detective, M, interp]

end Tests
end Noneism
end HeytingLean
