import Mathlib
import HeytingLean.PDE.Core

namespace HeytingLean.PDE

structure SchauderGateParams where
  n : Nat
  pExponent : Rat
  qExponent : Rat
  alpha : Rat
  hn : 2 ≤ n
  hp : (1 : Rat) < pExponent
  hpq : pExponent ≤ qExponent
  hAlpha : (0 : Rat) < alpha ∧ alpha ≤ 1
  hgap : qExponent / pExponent < 1 + alpha / (n : Rat)

structure PQGrowthBounds where
  cLower : Rat
  cUpper : Rat
  qMinusPExponent : Rat
  ellipticityTag : String
  deriving Repr, Inhabited

structure SchauderGateCert where
  params : SchauderGateParams
  coeffHolderConstant : Rat
  coeffHolderExponent : Rat
  growth : PQGrowthBounds
  sourceRef : String
  assumptions : List String := []

namespace SchauderGateCert

lemma alpha_pos (cert : SchauderGateCert) : (0 : Rat) < cert.params.alpha :=
  cert.params.hAlpha.1

lemma alpha_le_one (cert : SchauderGateCert) : cert.params.alpha ≤ (1 : Rat) :=
  cert.params.hAlpha.2

lemma dim_ge_two (cert : SchauderGateCert) : 2 ≤ cert.params.n :=
  cert.params.hn

end SchauderGateCert

structure SchauderConsequence (cert : SchauderGateCert) where
  gradientHolder : Prop
  localEnergyBound : Prop

end HeytingLean.PDE
