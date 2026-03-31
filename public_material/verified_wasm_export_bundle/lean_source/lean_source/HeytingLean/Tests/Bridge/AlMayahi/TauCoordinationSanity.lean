import HeytingLean.Bridge.AlMayahi.TauCoordination.Bridge

/-!
# TauCoordination Sanity
-/

namespace HeytingLean.Tests.Bridge.AlMayahi

open scoped BigOperators
open HeytingLean.Bridge.AlMayahi.TauCoordination

#check tau_quality_geq
#check tau_bias_leq
#check tau_asymptotic_optimality
#check spam_resistance
#check miftMonitorRuntime

example (net : AgentNetwork) : (∑ i : Fin net.n, tauWeight net i) = 1 :=
  tauWeight_sum net

example (net : AgentNetwork) : 0 ≤ consensusBias net .tauNormalized :=
  consensusBias_nonneg net .tauNormalized

example (net : AgentNetwork) : 0 ≤ rho net :=
  rho_nonneg net

#eval ("tau-coordination-monitor-smoke", miftMonitorRuntime 5 9 0.6)

end HeytingLean.Tests.Bridge.AlMayahi
