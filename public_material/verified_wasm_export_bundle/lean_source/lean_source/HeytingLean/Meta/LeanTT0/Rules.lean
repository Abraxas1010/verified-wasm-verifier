import HeytingLean.Meta.LeanTT0.Hash

namespace HeytingLean.Meta.LeanTT0

inductive KernelRule
  | BetaLamApp
  | DeltaPrimNatAdd
  deriving BEq, Inhabited

def serializeRule : KernelRule → ByteArray
  | .BetaLamApp       => "RuleID:KernelRule:BetaLamApp".toUTF8
  | .DeltaPrimNatAdd  => "RuleID:KernelRule:DeltaPrimNatAdd".toUTF8

structure RuleID where
  hash : ByteArray
  deriving BEq

  -- Hash utility (pure Lean, domain-separated)
  def ruleId (r : KernelRule) : RuleID :=
    ⟨H "LoF.RuleID|" (serializeRule r)⟩

end HeytingLean.Meta.LeanTT0
