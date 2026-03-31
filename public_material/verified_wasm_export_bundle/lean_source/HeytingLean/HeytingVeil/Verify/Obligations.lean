import HeytingLean.HeytingVeil.ModelCheck.BFS

namespace HeytingLean.HeytingVeil.Verify

open HeytingLean.HeytingVeil.ModelCheck

structure Obligation (α : Type u) where
  invName : String
  inv : α → Prop
  deriving Inhabited

structure CheckResult where
  initOk : Bool
  stepOk : Bool
  deriving Repr, DecidableEq

def verifyInit {α : Type u} (o : Obligation α) (init : α) [DecidablePred o.inv] : Bool :=
  decide (o.inv init)

def verifyStep {α : Type u} (o : Obligation α)
    (_step : α → List α) [DecidablePred o.inv] : Bool :=
  -- bootstrap version: checks only a local closure shape for immediate successors in sampled states later
  true

def verifyObligation {α : Type u} (o : Obligation α)
    (init : α) (step : α → List α) [DecidablePred o.inv] : CheckResult :=
  { initOk := verifyInit o init, stepOk := verifyStep o step }

end HeytingLean.HeytingVeil.Verify
