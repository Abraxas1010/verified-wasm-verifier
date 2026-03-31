import Mathlib.Algebra.Group.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm
import Mathlib.Algebra.FreeMonoid

/-!
# Trace monoids for rewrite concurrency

We model local update events as generators of a free monoid together with a
symmetry/independence relation.  Quotienting by the commutations induced by
independence yields the classical Mazurkiewicz trace monoid.  This module
provides the definitions and basic lemmas required to express causal
invariance (commutation of independent updates) in the contracts layer.

Note (Generative tie‑in): This concurrency view complements the plan’s
“no reason to stop”/stabilisation narrative: repeated application of a
stabiliser `R` iterates towards fixed points, while independence facts
describe when local update order is irrelevant. We keep this module
lightweight and independent of the generative machinery; it serves as a
documentation bridge.
-/

namespace HeytingLean
namespace Logic
namespace Trace

/-- Independence relation describing which events commute. -/
structure Independence (Σ : Type u) where
  rel : Σ → Σ → Prop
  symm : Symmetric rel
  irrefl : ∀ a, ¬ rel a a

attribute [simp] Independence.irrefl

namespace Independence

variable {Σ : Type u} (I : Independence Σ)

@[simp] lemma rel_symm {a b : Σ} : I.rel a b → I.rel b a :=
  I.symm

end Independence

/-- Words of commuting events; we reuse `List Σ` with the free-monoid
structure.  -/
abbrev Word (Σ : Type u) := List Σ

namespace Word

variable {Σ : Type u} (I : Independence Σ)

/-- Elementary swap of adjacent commuting events. -/
inductive Step : Word Σ → Word Σ → Prop
  | mk {l r : List Σ} {a b : Σ} :
      I.rel a b → Step (l ++ a :: b :: r) (l ++ b :: a :: r)

@[simp] lemma step_symm {w₁ w₂ : Word Σ}
    (h : Step (I := I) w₁ w₂) : Step (I := I) w₂ w₁ := by
  cases h with
  | mk hrel =>
      have := I.rel_symm hrel
      simpa [List.append_assoc] using
        Step.mk (I := I) (l := _) (r := _) this

/-- Reflexive-transitive closure of commuting steps. -/
def Congruence := Relation.ReflTransGen (Step (I := I))

@[simp] lemma congr_refl (w : Word Σ) : Congruence (I := I) w w :=
  Relation.ReflTransGen.refl

lemma congr_symm {w₁ w₂ : Word Σ}
    (h : Congruence (I := I) w₁ w₂) :
    Congruence (I := I) w₂ w₁ :=
  Relation.ReflTransGen.swap _ _ (by intro _ _ p; exact Step.step_symm (I := I) p) h

lemma congr_trans {w₁ w₂ w₃ : Word Σ}
    (h₁ : Congruence (I := I) w₁ w₂)
    (h₂ : Congruence (I := I) w₂ w₃) :
    Congruence (I := I) w₁ w₃ :=
  Relation.ReflTransGen.trans h₁ h₂

end Word

/-- The trace monoid is the quotient of the free monoid by the `Step`
congruence. -/
def TraceMonoid (Σ : Type u) (I : Independence Σ) :=
  Quot (Word.Congruence (I := I))

namespace TraceMonoid

variable {Σ : Type u} {I : Independence Σ}

/-- Lift words to traces. -/
def mk (w : Word Σ) : TraceMonoid Σ I := Quot.mk _ w

/-- Two words represent the same trace iff they are connected by commuting
steps. -/
@[simp] lemma mk_eq_mk {w₁ w₂ : Word Σ} :
    mk (I := I) w₁ = mk (I := I) w₂ ↔
      Word.Congruence (I := I) w₁ w₂ :=
  Iff.intro (fun h => Quot.eq.mp h) (fun h => Quot.eq.mpr h)

/-- The empty trace. -/
def empty : TraceMonoid Σ I := mk (I := I) []

/-- Multiplication defined via concatenation on representatives. -/
def mul : TraceMonoid Σ I → TraceMonoid Σ I → TraceMonoid Σ I :=
  Quot.map₂ (fun xs ys => mk (I := I) (xs ++ ys))
    (by
      intro xs xs' ys ys' hx hy
      refine Quot.eq.mpr ?_
      have hx' := Relation.ReflTransGen.append_right hx ys
      have hy' := Relation.ReflTransGen.append_left xs hy
      exact Relation.ReflTransGen.trans hx' hy')

instance : One (TraceMonoid Σ I) := ⟨empty (I := I)⟩

instance : Mul (TraceMonoid Σ I) := ⟨mul (I := I)⟩

@[simp] lemma mk_mul (w₁ w₂ : Word Σ) :
    (mk (I := I) w₁) * (mk (I := I) w₂)
      = mk (I := I) (w₁ ++ w₂) := rfl

@[simp] lemma mul_mk_mk (w₁ w₂ : Word Σ) :
    (mul (I := I) (mk (I := I) w₁) (mk (I := I) w₂))
      = mk (I := I) (w₁ ++ w₂) := rfl

@[simp] lemma mk_nil : mk (I := I) ([] : Word Σ) = (1 : TraceMonoid Σ I) := rfl

@[simp] lemma mul_assoc (a b c : TraceMonoid Σ I) :
    (a * b) * c = a * (b * c) := by
  refine Quot.induction_on₃ a b c ?_ ; intro x y z
  simp [mul, List.append_assoc]

@[simp] lemma one_mul (a : TraceMonoid Σ I) : (1 : TraceMonoid Σ I) * a = a := by
  refine Quot.induction_on a ?_ ; intro x
  simp [mul]

@[simp] lemma mul_one (a : TraceMonoid Σ I) : a * (1 : TraceMonoid Σ I) = a := by
  refine Quot.induction_on a ?_ ; intro x
  simp [mul]

instance : Semigroup (TraceMonoid Σ I) where
  mul := (· * ·)
  mul_assoc := mul_assoc (I := I)

instance : Monoid (TraceMonoid Σ I) where
  mul := (· * ·)
  one := 1
  mul_assoc := mul_assoc (I := I)
  one_mul := one_mul (I := I)
  mul_one := mul_one (I := I)

/-- Inclusion of generators into the trace monoid. -/
def of (a : Σ) : TraceMonoid Σ I := mk (I := I) [a]

@[simp] lemma of_mul_of {a b : Σ} (h : I.rel a b) :
    of (I := I) a * of (I := I) b = of (I := I) b * of (I := I) a := by
  have : Word.Step (I := I) ([a] : Word Σ) ([b]) := by
    simpa using Word.Step.mk (I := I) (l := []) (r := []) h
  have : Word.Congruence (I := I) [a,b] [b,a] :=
    Relation.ReflTransGen.single this
  simpa [of, mul, List.append_assoc]

end TraceMonoid

/-- A concurrency system associates to each trace of events its action on a
state space.  -/
structure ConcurrencySystem (Σ : Type u) (I : Independence Σ) where
  State : Type v
  actWord : Word Σ → State → State
  act_nil : ∀ s, actWord [] s = s
  act_cons : ∀ a w s, actWord (a :: w) s = actWord w (actWord [a] s)
  act_comm : ∀ {a b : Σ} {l r : List Σ},
    I.rel a b →
      ∀ s, actWord (l ++ a :: b :: r) s = actWord (l ++ b :: a :: r) s

namespace ConcurrencySystem

variable {Σ : Type u} {I : Independence Σ}

def actTrace (C : ConcurrencySystem Σ I) : TraceMonoid Σ I → C.State → C.State :=
  Quot.rec (fun w s => C.actWord w s) (by
    intro w₁ w₂ h
    apply funext; intro s
    induction h with
    | refl => rfl
    | tail w' w₁₂ h₁₂ ih =>
        cases h₁₂ with
        | mk hrel =>
            have hswap := C.act_comm (a := _) (b := _) (l := _) (r := _) hrel s
            have := congrArg (fun f => f s) ih
            exact this.trans hswap)

@[simp] lemma actTrace_mk (C : ConcurrencySystem Σ I)
    (w : Word Σ) (s : C.State) :
    C.actTrace (TraceMonoid.mk (I := I) w) s = C.actWord w s := rfl

/-- Causal invariance: the action factors through the trace monoid. -/
lemma actTrace_well_defined (C : ConcurrencySystem Σ I)
    {w₁ w₂ : Word Σ}
    (h : Word.Congruence (I := I) w₁ w₂) (s : C.State) :
    C.actWord w₁ s = C.actWord w₂ s := by
  induction h with
  | refl => rfl
  | tail w₂ w₃ h23 ih =>
      cases h23 with
      | mk hrel =>
          have hswap := C.act_comm (l := _) (r := _) hrel
          simpa [List.append_assoc] using
            funext (fun s => (ih s).trans (hswap s))

/-- Acting with the empty trace leaves the state unchanged. -/
@[simp] lemma actTrace_one (C : ConcurrencySystem Σ I) (s : C.State) :
    C.actTrace (1 : Trace.TraceMonoid Σ I) s = s := by
  change C.actWord [] s = s
  simpa using C.act_nil s

/-- Trace action composes multiplicatively. -/
@[simp] lemma actTrace_mul (C : ConcurrencySystem Σ I)
    (x y : Trace.TraceMonoid Σ I) (s : C.State) :
    C.actTrace (x * y) s = C.actTrace y (C.actTrace x s) := by
  refine Quot.induction_on₂ x y ?_ ; intro w₁ w₂
  change C.actWord (w₁ ++ w₂) s =
      C.actWord w₂ (C.actWord w₁ s)
  induction w₁ generalizing s with
  | nil =>
      simp [C.act_nil]
  | cons a w ih =>
      intro s
      simp [C.act_cons, ih, List.append_assoc]

end ConcurrencySystem

end Trace
end Logic
end HeytingLean
