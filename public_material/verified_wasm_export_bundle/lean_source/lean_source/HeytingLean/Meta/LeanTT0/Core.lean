import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.Meta.LeanTT0.Rules

/-!
Tiny TT0 core: untyped λ-calculus with β/δ for demo purposes.
This is sufficient to drive the β-only transcript and certificate flow.
-/

namespace HeytingLean.Meta.LeanTT0

inductive Tm where
  | var : String → Tm
  | lam : String → Tm → Tm
  | app : Tm → Tm → Tm
  | nat : Nat → Tm
  | primAdd : Tm     -- primitive nat addition
  deriving BEq, Inhabited

private def serializeVar (x : String) : String := x

def serializeTerm : Tm → String
  | .var x     => serializeVar x
  | .lam x b   => s!"(lam {x}. {serializeTerm b})"
  | .app f a   => s!"({serializeTerm f} {serializeTerm a})"
  | .nat n     => s!"{n}"
  | .primAdd   => "add"

def digestTerm (t : Tm) : ByteArray :=
  H "LoF.TT0.Term|" (serializeTerm t |>.toUTF8)

/- naive substitution without capture avoidance (ok for demo `(lam x. x) τ`) -/
def subst (b : Tm) (x : String) (a : Tm) : Tm :=
  match b with
  | .var y      => if y = x then a else b
  | .lam y body => if y = x then b else .lam y (subst body x a)
  | .app f a'   => .app (subst f x a) (subst a' x a)
  | .nat _      => b
  | .primAdd    => b

def stepBeta : Tm → Option Tm
  | .app (.lam x b) a => some (subst b x a)
  | _                 => none

def stepDelta (t : Tm) : Option Tm :=
  -- delta for nat addition: ((add n) m) ↦ (n+m)
  match t with
  | .app (.app .primAdd (.nat n)) (.nat m) => some (.nat (n + m))
  | _                                      => none

def applyRule (r : KernelRule) (t : Tm) : Option Tm :=
  match r with
  | .BetaLamApp      => stepBeta t
  | .DeltaPrimNatAdd => stepDelta t

end HeytingLean.Meta.LeanTT0
