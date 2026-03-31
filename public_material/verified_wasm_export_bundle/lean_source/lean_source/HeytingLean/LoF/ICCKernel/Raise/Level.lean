import Lean
import HeytingLean.LoF.ICCKernel.Lower.Level

namespace HeytingLean
namespace LoF
namespace ICCKernel
namespace Raise

def raiseName : Name → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (raiseName p) s
  | .num p n => .num (raiseName p) n

def raiseLevel : Level → Lean.Level
  | .zero => .zero
  | .succ u => .succ (raiseLevel u)
  | .max a b => .max (raiseLevel a) (raiseLevel b)
  | .imax a b => .imax (raiseLevel a) (raiseLevel b)
  | .param n => .param (raiseName n)
  | .mvar n => .mvar (.mk (raiseName n))

def raiseBinderInfo : BinderStyle → Lean.BinderInfo
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

def raiseLiteral : Literal → Lean.Literal
  | .nat n => .natVal n
  | .str s => .strVal s

theorem raiseName_lowerName (n : Lean.Name) :
    raiseName (Lower.lowerName n) = n := by
  induction n with
  | anonymous =>
      rfl
  | str p s ih =>
      simp [Lower.lowerName, raiseName, ih]
  | num p k ih =>
      simp [Lower.lowerName, raiseName, ih]

theorem raiseLevel_lowerLevel (u : Lean.Level) :
    raiseLevel (Lower.lowerLevel u) = u := by
  induction u with
  | zero =>
      rfl
  | succ u ih =>
      simp [Lower.lowerLevel, raiseLevel, ih]
  | max a b iha ihb =>
      simp [Lower.lowerLevel, raiseLevel, iha, ihb]
  | imax a b iha ihb =>
      simp [Lower.lowerLevel, raiseLevel, iha, ihb]
  | param n =>
      simp [Lower.lowerLevel, raiseLevel, raiseName_lowerName]
  | mvar n =>
      cases n
      simp [Lower.lowerLevel, raiseLevel, raiseName_lowerName]

theorem raiseBinderInfo_lowerBinderInfo (bi : Lean.BinderInfo) :
    raiseBinderInfo (Lower.lowerBinderInfo bi) = bi := by
  cases bi <;> rfl

end Raise
end ICCKernel
end LoF
end HeytingLean
