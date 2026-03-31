import HeytingLean.Crypto.QKD.E91.States
import HeytingLean.Crypto.QKD.E91.Tasks
import HeytingLean.Crypto.QKD.E91.Constructors
import HeytingLean.Crypto.QKD.E91.Superinfo
import HeytingLean.Crypto.QKD.E91.Eavesdropping
import HeytingLean.Crypto.QKD.E91.Security
import HeytingLean.Crypto.QKD.E91.Protocol
import HeytingLean.Crypto.QKD.E91.DeviceIndependent

/-!
# E91 Quantum Key Distribution (umbrella)

Interface-first umbrella for:
- the CT-native E91 toy instantiation (states/tasks/superinformation/eavesdropping security), and
- the CHSH/Tsirelson + device-independent layers (`Transcript`, certificates).
-/

namespace HeytingLean.Crypto.QKD.E91

-- Intentionally empty: importing the modules is the API.

end HeytingLean.Crypto.QKD.E91
