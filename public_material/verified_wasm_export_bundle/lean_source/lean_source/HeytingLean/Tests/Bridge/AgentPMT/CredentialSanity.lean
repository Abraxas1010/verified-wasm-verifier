import HeytingLean.Bridge.AgentPMT.CredentialLattice

namespace HeytingLean.Tests.Bridge.AgentPMT

open HeytingLean.Bridge.AgentPMT

private def budgetBinding : CredentialBinding :=
  { tier := .budget, requirementId := "r1", credentialId := "c1", payload := "user_key" }

private def budgetWideBinding : CredentialBinding :=
  { tier := .budgetWide, requirementId := "r1", credentialId := "c2", payload := "shared_key" }

private def masterBinding : CredentialBinding :=
  { tier := .master, requirementId := "r1", credentialId := "c3", payload := "master_key" }

example : mergeBindings budgetBinding masterBinding = masterBinding := by
  rfl

example : mergeBindings budgetBinding budgetWideBinding = budgetWideBinding := by
  rfl

example : mergeBindings masterBinding budgetBinding = masterBinding := by
  rfl

example : isRequirementSatisfied [budgetBinding, masterBinding] "r1" = true := by
  rfl

example : isRequirementSatisfied [] "google_oauth" = false := by
  rfl

#eval mergeBindings budgetBinding masterBinding
#eval isRequirementSatisfied [] "google_oauth"

end HeytingLean.Tests.Bridge.AgentPMT
