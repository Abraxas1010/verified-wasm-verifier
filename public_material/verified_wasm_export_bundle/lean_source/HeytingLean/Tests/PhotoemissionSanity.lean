import HeytingLean.Physics.Photoemission

/-!
# Sanity checks: photoemission physics layer

This module is intentionally lightweight: it ensures the photoemission API
imports cleanly and key theorems are available.
-/

namespace HeytingLean.Tests.PhotoemissionSanity

open HeytingLean.Physics.Photoemission

-- Efficiency layer
#check HeytingLean.Physics.Photoemission.efficiency_factorization

-- CT bridge constraints
#check HeytingLean.Physics.Photoemission.energy_conservation_required
#check HeytingLean.Physics.Photoemission.photoemissionTaskCT.possible_full_of_possible_steps

-- Coherence layer
#check HeytingLean.Physics.Photoemission.coherence_enhancement
#check HeytingLean.Physics.Photoemission.coherent_transport_superinfo

-- Hamiltonian / Golden rule layer
#check HeytingLean.Physics.Photoemission.absorption_from_golden_rule

end HeytingLean.Tests.PhotoemissionSanity

