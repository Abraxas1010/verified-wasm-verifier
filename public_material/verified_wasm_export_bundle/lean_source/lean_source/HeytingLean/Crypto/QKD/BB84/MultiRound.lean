import HeytingLean.Constructor.CT.MultiRound
import HeytingLean.Crypto.QKD.BB84.Security

/-!
# BB84 multi-round / composable reductions (CT-style)

This file provides a lightweight “multi-round” layer consistent with the current CT
formalization:

- We can *build* repeated tasks syntactically using `Task.seqPow`/`Task.parPow`.
- Security remains reduction-based: if an `n`-round attack would imply the ability to
  perform the forbidden single-round subtask `copyAll`, then the `n`-round attack is
  CT-impossible (by `bb84_composed_security`).

We intentionally avoid probability/entropy machinery here (interface-first).
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84

open HeytingLean.Constructor.CT

/-- A generic “multi-round” attack task (serial repetition at the syntax layer). -/
def attackSeqPow (n : ℕ) (attack : CTask BB84Substrate) : CTask BB84Substrate :=
  Task.seqPow n attack

/-- A generic “multi-round” attack task (parallel repetition at the syntax layer). -/
def attackParPow (n : ℕ) (attack : CTask BB84Substrate) : CTask BB84Substrate :=
  Task.parPow n attack

/-- Reduction principle (serial): any multi-round attack that implies `copyAll` is impossible. -/
theorem bb84_attackSeqPow_impossible (n : ℕ) (attack : CTask BB84Substrate)
    (h_requires : bb84TaskCT.possible (attackSeqPow n attack) → bb84TaskCT.possible copyAll) :
    bb84TaskCT.impossible (attackSeqPow n attack) :=
  bb84_composed_security (T_attack := attackSeqPow n attack) h_requires

/-- Reduction principle (parallel): any multi-round attack that implies `copyAll` is impossible. -/
theorem bb84_attackParPow_impossible (n : ℕ) (attack : CTask BB84Substrate)
    (h_requires : bb84TaskCT.possible (attackParPow n attack) → bb84TaskCT.possible copyAll) :
    bb84TaskCT.impossible (attackParPow n attack) :=
  bb84_composed_security (T_attack := attackParPow n attack) h_requires

end BB84
end QKD
end Crypto
end HeytingLean

