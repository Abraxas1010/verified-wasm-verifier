import Lean
import HeytingLean.LoF.ICCKernel.Syntax

namespace HeytingLean
namespace LoF
namespace ICCKernel
namespace Lower

def lowerName : Lean.Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (lowerName p) s
  | .num p n => .num (lowerName p) n

def lowerLevel : Lean.Level → Level
  | .zero => .zero
  | .succ u => .succ (lowerLevel u)
  | .max a b => .max (lowerLevel a) (lowerLevel b)
  | .imax a b => .imax (lowerLevel a) (lowerLevel b)
  | .param n => .param (lowerName n)
  | .mvar n => .mvar (lowerName n.name)

def lowerBinderInfo : Lean.BinderInfo → BinderStyle
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

theorem lowerName_never_anonymous_str {p s} :
    lowerName (.str p s) = .str (lowerName p) s := by
  rfl

theorem lowerLevel_total (u : Lean.Level) : ∃ v, lowerLevel u = v := by
  exact ⟨lowerLevel u, rfl⟩

end Lower
end ICCKernel
end LoF
end HeytingLean
