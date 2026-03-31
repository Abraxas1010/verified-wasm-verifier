import HeytingLean.DarwinsCage.Experiments.QuantumLaptopW1
import HeytingLean.DarwinsCage.Theorems.QuantumLearning

/-!
# Quantum Laptop theorems

Discharges the extended W1-style experiment goal using the generic quantum
learning theorem.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Theorems

open Experiments

theorem quantumLaptopW1_breaks_cage : Experiments.expW1.goal :=
  Theorems.expW1_quantum_breaks_cage Experiments.expW1

end Theorems
end DarwinsCage
end HeytingLean

