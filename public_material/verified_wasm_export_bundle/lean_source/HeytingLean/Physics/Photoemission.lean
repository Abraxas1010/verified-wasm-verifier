import HeytingLean.Physics.Substrate.Hilbert
import HeytingLean.Physics.Channels.CPTP
import HeytingLean.Physics.Photoemission.Tasks
import HeytingLean.Physics.Photoemission.CTBridge
import HeytingLean.Physics.Photoemission.Efficiency
import HeytingLean.Physics.Photoemission.Coherence
import HeytingLean.Physics.Photoemission.Hamiltonian

/-!
# Photoemission physics (Constructor Theory integration surface)

Umbrella module for the photoemission extension:
- typed Hilbert substrates + channels,
- three-step photoemission tasks,
- CT bridge (`TaskCT` instance + constraints),
- efficiency factorization (η = A · T · D),
- coherence and Golden Rule scaffolding.
-/

namespace HeytingLean.Physics.Photoemission

-- Intentionally empty: importing the modules is the API.

end HeytingLean.Physics.Photoemission

