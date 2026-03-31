import HeytingLean.Physics.String.Spec.QSeriesN

/-!
Simple closure operator over `QSeriesN` (spec-level) to exercise
extensive/monotone/idempotent laws in a lightweight setting.
We define `cl` as the identity function, which is a bona fide
closure operator and suffices for compile-only checks.
-/

namespace HeytingLean
namespace Physics
namespace String
namespace Spec

open QSeriesN

def lePointwise (a b : QSeriesN) : Prop :=
  ∀ i, a.coeffAt i ≤ b.coeffAt i

@[simp] theorem lePointwise_refl (a : QSeriesN) : lePointwise a a := by
  intro i; exact Nat.le_refl _

def cl (q : QSeriesN) : QSeriesN := q

@[simp] theorem cl_extensive (q : QSeriesN) : lePointwise q (cl q) := by
  intro i; simp [cl]

@[simp] theorem cl_idem (q : QSeriesN) : cl (cl q) = cl q := rfl

@[simp] theorem cl_mono {a b : QSeriesN} (h : lePointwise a b) :
    lePointwise (cl a) (cl b) := by
  simpa using h

end Spec
end String
end Physics
end HeytingLean
