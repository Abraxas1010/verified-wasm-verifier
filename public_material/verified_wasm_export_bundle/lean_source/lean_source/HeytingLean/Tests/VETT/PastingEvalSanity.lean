import HeytingLean.VETT.Rel.PastingEval
import HeytingLean.IteratedVirtual.PastingFramed

/-!
# Tests.VETT.PastingEvalSanity

Compile-time sanity checks that `PastingFramed` evaluation can compute relation semantics in the
strict VETT relation model.
-/

namespace HeytingLean.Tests.VETT.PastingEvalSanity

open HeytingLean.VETT.Rel
open HeytingLean.IteratedVirtual

namespace Example

open VETT.Rel.PastingEval

variable {A : Type} {B : Type} {C : Type}

variable (P : PastingEval.Horiz A B) (Q : PastingEval.Horiz B C)

/-- A 2-ary cell which interprets its two inputs by tensoring them, with identity frame. -/
def tensorCell :
    (PastingEval.V).Cell
      (n := 2)
      (A := fun
        | ⟨0, _⟩ => A
        | ⟨1, _⟩ => B
        | ⟨2, _⟩ => C)
      (B := fun
        | ⟨0, _⟩ => A
        | ⟨1, _⟩ => B
        | ⟨2, _⟩ => C)
      (v := fun
        | ⟨0, _⟩ => (fun x => x)
        | ⟨1, _⟩ => (fun x => x)
        | ⟨2, _⟩ => (fun x => x))
      (h := fun
        | ⟨0, _⟩ => P
        | ⟨1, _⟩ => Q)
      (tgt := PastingEval.upHoriz (fun a c => ∃ b, P.rel a b ∧ Q.rel b c)) :=
  { eval := fun args =>
      PastingEval.upHoriz (fun a c =>
        ∃ b, (args ⟨0, by decide⟩).rel a b ∧ (args ⟨1, by decide⟩).rel b c)
    sound := rfl }

def tensorDiagram :
    PastingFramed PastingEval.V
      (PastingEval.upHoriz (fun a c => ∃ b, P.rel a b ∧ Q.rel b c)) :=
  PastingFramed.cell (V := PastingEval.V)
    (n := 2)
    (A := fun
      | ⟨0, _⟩ => A
      | ⟨1, _⟩ => B
      | ⟨2, _⟩ => C)
    (B := fun
      | ⟨0, _⟩ => A
      | ⟨1, _⟩ => B
      | ⟨2, _⟩ => C)
    (v := fun
      | ⟨0, _⟩ => (fun x => x)
      | ⟨1, _⟩ => (fun x => x)
      | ⟨2, _⟩ => (fun x => x))
    (h := fun
      | ⟨0, _⟩ => P
      | ⟨1, _⟩ => Q)
    (tgt := PastingEval.upHoriz (fun a c => ∃ b, P.rel a b ∧ Q.rel b c))
    (tensorCell (A := A) (B := B) (C := C) P Q)
    (fun
      | ⟨0, _⟩ => PastingFramed.pure (V := PastingEval.V) P
      | ⟨1, _⟩ => PastingFramed.pure (V := PastingEval.V) Q)

example :
    PastingEval.evalRel (A := A) (B := C)
        (PastingEval.upHoriz (fun a c => ∃ b, P.rel a b ∧ Q.rel b c))
        (tensorDiagram (A := A) (B := B) (C := C) P Q) =
      PastingEval.upHoriz (fun a c => ∃ b, P.rel a b ∧ Q.rel b c) := by
  simpa [PastingEval.evalRel] using
    PastingEval.evalRel_eq (A := A) (B := C)
        (PastingEval.upHoriz (fun a c => ∃ b, P.rel a b ∧ Q.rel b c))
      (tensorDiagram (A := A) (B := B) (C := C) P Q)

end Example

end HeytingLean.Tests.VETT.PastingEvalSanity
