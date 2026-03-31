import HeytingLean.PTS.BaseExtension.Main

namespace HeytingLean
namespace ATP
namespace Ensemble

open PTS.BaseExtension

inductive GoalSkeleton where
  | atom : Atom → GoalSkeleton
  | bot : GoalSkeleton
  | conj : GoalSkeleton → GoalSkeleton → GoalSkeleton
  | disj : GoalSkeleton → GoalSkeleton → GoalSkeleton
  | imp : GoalSkeleton → GoalSkeleton → GoalSkeleton
  deriving DecidableEq, Repr

def GoalSkeleton.toIPL : GoalSkeleton → IPL
  | .atom a => .atom a
  | .bot => .bot
  | .conj φ ψ => .conj φ.toIPL ψ.toIPL
  | .disj φ ψ => .disj φ.toIPL ψ.toIPL
  | .imp φ ψ => .imp φ.toIPL ψ.toIPL

def extractIdentity (a : Atom) : GoalSkeleton :=
  .imp (.atom a) (.atom a)

def extractPeirce (p q : Atom) : GoalSkeleton :=
  .imp (.imp (.imp (.atom p) (.atom q)) (.atom p)) (.atom p)

def extractDoubleNegationElim (p : Atom) : GoalSkeleton :=
  let neg : GoalSkeleton → GoalSkeleton := fun φ => .imp φ .bot
  .imp (neg (neg (.atom p))) (.atom p)

end Ensemble
end ATP
end HeytingLean
