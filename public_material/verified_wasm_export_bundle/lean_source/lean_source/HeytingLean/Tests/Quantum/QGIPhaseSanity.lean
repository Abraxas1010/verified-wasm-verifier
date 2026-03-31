import HeytingLean.Quantum.QGIPhaseLaw

/-
Compile-only sanity checks for the symbolic QGI T³ phase law.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum
open HeytingLean.Quantum.QGIPhaseLaw

#check t3Phase
#check gaugePhase
#check t3PhaseR
#check gaugePhaseR
#check t3Phase_zero_g
#check gaugePhase_zero_g

end HeytingLean.Tests.Quantum
