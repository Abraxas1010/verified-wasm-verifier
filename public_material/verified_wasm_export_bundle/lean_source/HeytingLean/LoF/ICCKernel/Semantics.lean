import HeytingLean.LoF.ICCKernel.Syntax

/-!
# ICCKernel.Semantics

Minimal structural semantics for ICCKernel terms.
-/

namespace HeytingLean
namespace LoF
namespace ICCKernel

namespace Term

def size : Term → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .mvar _ => 1
  | .sort _ => 1
  | .const _ _ => 1
  | .app f a => f.size + a.size + 1
  | .lam _ _ ty body => ty.size + body.size + 1
  | .forallE _ _ ty body => ty.size + body.size + 1
  | .letE _ ty val body _ => ty.size + val.size + body.size + 1
  | .lit _ => 1
  | .mdata _ body => body.size + 1
  | .proj _ _ body => body.size + 1
  | .bridge body => body.size + 1
  | .ann val typ => val.size + typ.size + 1

def containsBridge : Term → Bool
  | .bridge _ => true
  | .app f a => containsBridge f || containsBridge a
  | .lam _ _ ty body => containsBridge ty || containsBridge body
  | .forallE _ _ ty body => containsBridge ty || containsBridge body
  | .letE _ ty val body _ => containsBridge ty || containsBridge val || containsBridge body
  | .mdata _ body => containsBridge body
  | .proj _ _ body => containsBridge body
  | .ann val typ => containsBridge val || containsBridge typ
  | _ => false

def containsAnn : Term → Bool
  | .ann _ _ => true
  | .app f a => containsAnn f || containsAnn a
  | .lam _ _ ty body => containsAnn ty || containsAnn body
  | .forallE _ _ ty body => containsAnn ty || containsAnn body
  | .letE _ ty val body _ => containsAnn ty || containsAnn val || containsAnn body
  | .mdata _ body => containsAnn body
  | .proj _ _ body => containsAnn body
  | .bridge body => containsAnn body
  | _ => false

def closedAbove : Nat → Term → Prop
  | k, .bvar idx => idx < k
  | _, .fvar _ => True
  | _, .mvar _ => True
  | _, .sort _ => True
  | _, .const _ _ => True
  | k, .app f a => closedAbove k f ∧ closedAbove k a
  | k, .lam _ _ ty body => closedAbove k ty ∧ closedAbove (k + 1) body
  | k, .forallE _ _ ty body => closedAbove k ty ∧ closedAbove (k + 1) body
  | k, .letE _ ty val body _ => closedAbove k ty ∧ closedAbove k val ∧ closedAbove (k + 1) body
  | _, .lit _ => True
  | k, .mdata _ body => closedAbove k body
  | k, .proj _ _ body => closedAbove k body
  | k, .bridge body => closedAbove (k + 1) body
  | k, .ann val typ => closedAbove k val ∧ closedAbove k typ

abbrev Closed (t : Term) : Prop :=
  closedAbove 0 t

def containsFallbackMarker (_ : Term) : Bool :=
  false

theorem noFallbackMarker (t : Term) : containsFallbackMarker t = false := by
  rfl

end Term

end ICCKernel
end LoF
end HeytingLean
