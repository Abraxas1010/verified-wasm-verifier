import HeytingLean.LoF.ICC.Syntax
import HeytingLean.LoF.Combinators.SKY

namespace HeytingLean
namespace LoF
namespace ICC

open HeytingLean.LoF

def kTerm : Term :=
  .lam (.lam (.var 1))

def sTerm : Term :=
  .lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))

/--
Local compatibility shim for the legacy SKY `Y` combinator.

This is not claimed as public ICC syntax. It is a closed term built from the
public constructors so the additive lane can preserve current SKY behavior
without mutating the production `Comb` type.
-/
def legacyY : Term :=
  .bridge (.ann (.var 0) (.var 0))

def embedLegacy : LoF.Comb → Term
  | .K => kTerm
  | .S => sTerm
  | .Y => legacyY
  | .app fn arg => .app (embedLegacy fn) (embedLegacy arg)

def eraseLegacy? : Term → Option LoF.Comb
  | .app fn arg =>
      match eraseLegacy? fn, eraseLegacy? arg with
      | some fn', some arg' => some (.app fn' arg')
      | _, _ => none
  | t =>
      if t = kTerm then
        some .K
      else if t = sTerm then
        some .S
      else if t = legacyY then
        some .Y
      else
        none

def legacyContainsY : LoF.Comb → Bool
  | .K => false
  | .S => false
  | .Y => true
  | .app fn arg => legacyContainsY fn || legacyContainsY arg

def legacyImage (t : Term) : Prop :=
  ∃ c : LoF.Comb, embedLegacy c = t

@[simp] theorem closed_kTerm : Term.Closed kTerm := by
  simp [kTerm, Term.Closed, Term.closedAbove]

@[simp] theorem closed_sTerm : Term.Closed sTerm := by
  simp [sTerm, Term.Closed, Term.closedAbove]

@[simp] theorem closed_legacyY : Term.Closed legacyY := by
  simp [legacyY, Term.Closed, Term.closedAbove]

@[simp] theorem closed_embedLegacy (t : LoF.Comb) : Term.Closed (embedLegacy t) := by
  induction t with
  | K => simp [embedLegacy, kTerm, Term.Closed, Term.closedAbove]
  | S => simp [embedLegacy, sTerm, Term.Closed, Term.closedAbove]
  | Y => simp [embedLegacy, legacyY, Term.Closed, Term.closedAbove]
  | app fn arg ihFn ihArg =>
      simp [embedLegacy, Term.Closed, Term.closedAbove, ihFn, ihArg]

@[simp] theorem erase_embedLegacy (t : LoF.Comb) :
    eraseLegacy? (embedLegacy t) = some t := by
  induction t with
  | K =>
      native_decide
  | S =>
      native_decide
  | Y =>
      native_decide
  | app fn arg ihFn ihArg =>
      simp [embedLegacy, eraseLegacy?, ihFn, ihArg]

end ICC
end LoF
end HeytingLean
