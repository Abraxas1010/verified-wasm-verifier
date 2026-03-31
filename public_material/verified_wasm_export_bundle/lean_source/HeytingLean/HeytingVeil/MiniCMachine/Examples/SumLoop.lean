import HeytingLean.HeytingVeil.MiniCMachine.Decidable
import HeytingLean.HeytingVeil.ModelCheck.VerifyLoop

namespace HeytingLean
namespace HeytingVeil
namespace MiniCMachine
namespace Examples

def sumToFun : MiniC.Fun :=
  {
    name := "sum_to_or_zero"
    params := ["n"]
    body :=
      .if_ (.le (.var "n") (.intLit 0))
        (.return (.intLit 0))
        (.seq
          (.assign "i" (.intLit 0))
          (.seq
            (.assign "s" (.intLit 0))
            (.seq
              (.while (.le (.var "i") (.var "n"))
                (.seq
                  (.assign "s" (.add (.var "s") (.var "i")))
                  (.assign "i" (.add (.var "i") (.intLit 1)))))
              (.return (.var "s")))))
  }

def sumDomain : BoundedDomain :=
  { vars := [("n", 0, 3), ("i", 0, 4), ("s", 0, 12)] }

def sumMachine : ModelCheck.DecidableMachine ProgramConfig :=
  boundedMiniCMachine sumToFun [] sumDomain

def sumLoopInvariant (cfg : ProgramConfig) : Prop :=
  let i := cfg.store.lookup "i"
  let s := cfg.store.lookup "s"
  let n := cfg.store.lookup "n"
  0 ≤ i ∧ i ≤ n + 1 ∧ s = (i * (i - 1)) / 2

def sumWeakInvariant (cfg : ProgramConfig) : Prop :=
  let i := cfg.store.lookup "i"
  let n := cfg.store.lookup "n"
  0 ≤ i ∧ i ≤ n + 1

instance : DecidablePred sumLoopInvariant := by
  intro cfg
  unfold sumLoopInvariant
  infer_instance

instance : DecidablePred sumWeakInvariant := by
  intro cfg
  unfold sumWeakInvariant
  infer_instance

def sumWeakCandidate : ModelCheck.DecidableInvCandidate ProgramConfig :=
  {
    inv := sumWeakInvariant
    decInv := by
      intro s
      exact (by infer_instance : Decidable (sumWeakInvariant s))
  }

#eval checkSafety sumMachine sumLoopInvariant 8
#eval (ModelCheck.verifyRefineLoop sumMachine sumWeakCandidate 8 4).refinements
#eval (ModelCheck.verifyRefineLoop sumMachine sumWeakCandidate 8 4).unresolvedCTI

end Examples
end MiniCMachine
end HeytingVeil
end HeytingLean
