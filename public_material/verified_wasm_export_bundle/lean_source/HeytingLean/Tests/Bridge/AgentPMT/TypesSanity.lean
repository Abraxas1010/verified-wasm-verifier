import HeytingLean.Bridge.AgentPMT.Types

namespace HeytingLean.Tests.Bridge.AgentPMT

open HeytingLean.Bridge.AgentPMT

example : HttpMethod.asToken .POST = "POST" := by
  rfl

example : BindingTier.budget ≤ BindingTier.master := by
  trivial

example : ¬ BindingTier.master ≤ BindingTier.budget := by
  intro h
  cases h

example : defaultRequest.path = "/" := by
  rfl

#eval HttpMethod.asToken .POST
#eval defaultRequest

end HeytingLean.Tests.Bridge.AgentPMT
