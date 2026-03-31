import HeytingLean.Bridge.INet

namespace HeytingLean.Tests.Bridge

open HeytingLean.Bridge.INet
open HeytingLean.LoF

#check SKYAgent
#check Port
#check AgentNode
#check INet
#check encodeComb
#check InteractionRule
#check RuleSummary
#check stagedRuleForKinds?

example : SKYAgent.arity .app = 2 := rfl
example : SKYAgent.isLeaf .y = true := rfl
example : SKYAgent.isLeaf .dup = false := rfl

example : (INet.singleton .k).agentCount = 1 := rfl
example : (INet.singleton .s).isNormalForm := by
  rfl

example : stagedRuleForKinds? .app .k1 = some .kStage2 := rfl
example : stagedRuleForKinds? .app .y = some .yStage := rfl

def sampleComb : LoF.Comb :=
  .app (.app .K .S) .Y

example : (encodeComb sampleComb).agentCount = 5 := rfl

end HeytingLean.Tests.Bridge
