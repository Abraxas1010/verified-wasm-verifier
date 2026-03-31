import Mathlib

namespace HeytingLean.PadicDecoupling.Hamiltonian

abbrev Energy := ℝ

structure TripartiteHamiltonian where
  E_worker : Energy
  E_signal : Energy
  E_interaction : Energy
  worker_nonneg : 0 ≤ E_worker
  signal_nonneg : 0 ≤ E_signal
  interaction_nonneg : 0 ≤ E_interaction

def TripartiteHamiltonian.total (H : TripartiteHamiltonian) : Energy :=
  H.E_worker + H.E_signal + H.E_interaction

theorem interaction_cancellation (δ h_worker_loss h_signal_gain h_int_gain : ℝ)
    (h_split : h_signal_gain + h_int_gain = δ) (h_loss : h_worker_loss = -δ) :
    h_worker_loss + h_signal_gain + h_int_gain = 0 := by
  calc
    h_worker_loss + h_signal_gain + h_int_gain = -δ + (h_signal_gain + h_int_gain) := by
      rw [h_loss]
      ring
    _ = 0 := by
      rw [h_split]
      ring

end HeytingLean.PadicDecoupling.Hamiltonian
