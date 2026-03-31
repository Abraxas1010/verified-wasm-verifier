import HeytingLean.PadicDecoupling.Hamiltonian.Tripartite

namespace HeytingLean.PadicDecoupling.Hamiltonian

structure TimeStep where
  before : TripartiteHamiltonian
  after : TripartiteHamiltonian
  transfer : ℝ
  transfer_nonneg : 0 ≤ transfer
  signal_fraction : ℝ
  fraction_bounds : 0 ≤ signal_fraction ∧ signal_fraction ≤ 1
  worker_decrease : after.E_worker = before.E_worker - transfer
  signal_increase : after.E_signal = before.E_signal + transfer * signal_fraction
  interaction_increase :
    after.E_interaction = before.E_interaction + transfer * (1 - signal_fraction)

theorem step_conserves_energy (ts : TimeStep) :
    ts.after.total = ts.before.total := by
  unfold TripartiteHamiltonian.total
  rw [ts.worker_decrease, ts.signal_increase, ts.interaction_increase]
  ring

end HeytingLean.PadicDecoupling.Hamiltonian
