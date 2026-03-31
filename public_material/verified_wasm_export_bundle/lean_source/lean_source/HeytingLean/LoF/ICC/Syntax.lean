/-!
# ICC.Syntax

Experimental ICC syntax for the additive SKY research lane.

This file intentionally mirrors the audited public ICC gist facts:

- the public AST includes `Var` explicitly
- the bridge-like constructor is spelled `Val` in the public source and printed as `θ`

The local Lean name `bridge` corresponds to that public `Val` constructor.
This file does not claim that the entire ICC operational story is already
verified in this repo.
-/

namespace HeytingLean
namespace LoF
namespace ICC

inductive Term where
  | var (idx : Nat)
  | lam (body : Term)
  | app (fn arg : Term)
  | bridge (body : Term)
  | ann (val typ : Term)
deriving DecidableEq, Repr

namespace Term

def size : Term → Nat
  | .var _ => 1
  | .lam body => body.size + 1
  | .app fn arg => fn.size + arg.size + 1
  | .bridge body => body.size + 1
  | .ann val typ => val.size + typ.size + 1

def containsBridge : Term → Bool
  | .var _ => false
  | .lam body => containsBridge body
  | .app fn arg => containsBridge fn || containsBridge arg
  | .bridge _ => true
  | .ann val typ => containsBridge val || containsBridge typ

def containsAnn : Term → Bool
  | .var _ => false
  | .lam body => containsAnn body
  | .app fn arg => containsAnn fn || containsAnn arg
  | .bridge body => containsAnn body
  | .ann _ _ => true

def bridgeFree (t : Term) : Bool :=
  !t.containsBridge

def annFree (t : Term) : Bool :=
  !t.containsAnn

private def shiftIndex (cutoff inc idx : Nat) : Nat :=
  if idx >= cutoff then idx + inc else idx

def shiftAbove : Term → Nat → Nat → Term
  | .var idx, cutoff, inc => .var (shiftIndex cutoff inc idx)
  | .lam body, cutoff, inc => .lam (shiftAbove body (cutoff + 1) inc)
  | .app fn arg, cutoff, inc => .app (shiftAbove fn cutoff inc) (shiftAbove arg cutoff inc)
  | .bridge body, cutoff, inc => .bridge (shiftAbove body (cutoff + 1) inc)
  | .ann val typ, cutoff, inc => .ann (shiftAbove val cutoff inc) (shiftAbove typ cutoff inc)

def shift (t : Term) (inc : Nat) : Term :=
  shiftAbove t 0 inc

def substAt (cutoff : Nat) (repl : Term) : Term → Term
  | .var idx =>
      if idx = cutoff then
        shiftAbove repl 0 cutoff
      else if cutoff < idx then
        .var (idx - 1)
      else
        .var idx
  | .lam body => .lam (substAt (cutoff + 1) repl body)
  | .app fn arg => .app (substAt cutoff repl fn) (substAt cutoff repl arg)
  | .bridge body => .bridge (substAt (cutoff + 1) repl body)
  | .ann val typ => .ann (substAt cutoff repl val) (substAt cutoff repl typ)

def subst0 (repl body : Term) : Term :=
  substAt 0 repl body

def closedAbove : Nat → Term → Prop
  | k, .var idx => idx < k
  | k, .lam body => closedAbove (k + 1) body
  | k, .app fn arg => closedAbove k fn ∧ closedAbove k arg
  | k, .bridge body => closedAbove (k + 1) body
  | k, .ann val typ => closedAbove k val ∧ closedAbove k typ

abbrev Closed (t : Term) : Prop :=
  closedAbove 0 t

@[simp] theorem shiftAbove_closedAbove_eq {k inc : Nat} {t : Term}
    (h : closedAbove k t) :
    shiftAbove t k inc = t := by
  induction t generalizing k with
  | var idx =>
      simp [closedAbove] at h
      simp [shiftAbove, shiftIndex, Nat.not_le_of_gt h]
  | lam body ih =>
      simp [closedAbove] at h
      simp [shiftAbove, ih h]
  | app fn arg ihFn ihArg =>
      rcases h with ⟨hFn, hArg⟩
      simp [shiftAbove, ihFn hFn, ihArg hArg]
  | bridge body ih =>
      simp [closedAbove] at h
      simp [shiftAbove, ih h]
  | ann val typ ihVal ihTyp =>
      rcases h with ⟨hVal, hTyp⟩
      simp [shiftAbove, ihVal hVal, ihTyp hTyp]

@[simp] theorem shift_closed {t : Term} (h : Closed t) (inc : Nat) :
    shift t inc = t := by
  simpa [shift, Closed] using (shiftAbove_closedAbove_eq (k := 0) (inc := inc) h)

@[simp] theorem substAt_closedAbove_eq {k : Nat} {repl t : Term}
    (h : closedAbove k t) :
    substAt k repl t = t := by
  induction t generalizing k with
  | var idx =>
      simp [closedAbove] at h
      have hNe : idx ≠ k := Nat.ne_of_lt h
      have hNotLt : ¬ k < idx := Nat.not_lt_of_ge (Nat.le_of_lt h)
      simp [substAt, hNe, hNotLt]
  | lam body ih =>
      simp [closedAbove] at h
      simp [substAt, ih h]
  | app fn arg ihFn ihArg =>
      rcases h with ⟨hFn, hArg⟩
      simp [substAt, ihFn hFn, ihArg hArg]
  | bridge body ih =>
      simp [closedAbove] at h
      simp [substAt, ih h]
  | ann val typ ihVal ihTyp =>
      rcases h with ⟨hVal, hTyp⟩
      simp [substAt, ihVal hVal, ihTyp hTyp]

@[simp] theorem substAt_closedAbove_ge {k cutoff : Nat} {repl t : Term}
    (h : closedAbove k t) (hcut : k ≤ cutoff) :
    substAt cutoff repl t = t := by
  induction t generalizing k cutoff with
  | var idx =>
      simp [closedAbove] at h
      have hlt : idx < cutoff := Nat.lt_of_lt_of_le h hcut
      have hNe : idx ≠ cutoff := Nat.ne_of_lt hlt
      have hNotLt : ¬ cutoff < idx := Nat.not_lt_of_ge (Nat.le_of_lt hlt)
      simp [substAt, hNe, hNotLt]
  | lam body ih =>
      simp [closedAbove] at h
      have hcut' : k + 1 ≤ cutoff + 1 := Nat.succ_le_succ hcut
      simp [substAt, ih h hcut']
  | app fn arg ihFn ihArg =>
      rcases h with ⟨hFn, hArg⟩
      simp [substAt, ihFn hFn hcut, ihArg hArg hcut]
  | bridge body ih =>
      simp [closedAbove] at h
      have hcut' : k + 1 ≤ cutoff + 1 := Nat.succ_le_succ hcut
      simp [substAt, ih h hcut']
  | ann val typ ihVal ihTyp =>
      rcases h with ⟨hVal, hTyp⟩
      simp [substAt, ihVal hVal hcut, ihTyp hTyp hcut]

@[simp] theorem subst0_closed {repl t : Term} (h : Closed t) :
    subst0 repl t = t := by
  simpa [subst0, Closed] using (substAt_closedAbove_eq (k := 0) (repl := repl) h)

end Term

end ICC
end LoF
end HeytingLean
