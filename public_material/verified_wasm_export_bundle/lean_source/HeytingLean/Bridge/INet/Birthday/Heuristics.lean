import HeytingLean.Bridge.INet.Basic
import HeytingLean.LoF.Combinators.Birthday.Metric

namespace HeytingLean
namespace Bridge
namespace INet
namespace Birthday

open HeytingLean.LoF

/-- Lightweight structural load induced by the staged SKY interaction-net encoding. -/
def inetStructuralLoad (t : Comb) : Nat :=
  let net := encodeComb t
  net.agentCount + net.activePairs.length

@[simp] theorem inetStructuralLoad_K :
    inetStructuralLoad Comb.K = 1 := by
  rfl

@[simp] theorem inetStructuralLoad_S :
    inetStructuralLoad Comb.S = 1 := by
  rfl

@[simp] theorem inetStructuralLoad_Y :
    inetStructuralLoad Comb.Y = 1 := by
  rfl

end Birthday
end INet
end Bridge
end HeytingLean
