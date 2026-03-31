import HeytingLean.Topology.Knot.BracketMathlibReidemeisterR3

/-!
# Kauffman R3 Negative Targets

Concrete regression witnesses for unconditional endpoint-closure attempts.
-/

namespace HeytingLean.Tests.Topology.KauffmanR3NegativeTargets

open HeytingLean.Topology.Knot
open Kauffman

def r3UnconditionalCounterexampleGraph : PDGraph :=
  { freeLoops := 0
    n := 2
    arcNbr := #[1, 0, 5, 4, 3, 2, 7, 6] }

def r3_unconditional_counterexample_endpoints_ok_bool : Bool :=
  match Reidemeister.r3BraidLeft r3UnconditionalCounterexampleGraph 0 2 4,
      Reidemeister.r3BraidRight r3UnconditionalCounterexampleGraph 0 2 4 with
  | .ok _, .ok _ => true
  | _, _ => false

theorem r3_unconditional_counterexample_endpoints_ok :
    r3_unconditional_counterexample_endpoints_ok_bool = true := by
  native_decide

def execBracketEqBool (g1 g2 : PDGraph) : Bool :=
  match bracketGraph g1, bracketGraph g2 with
  | .ok p1, .ok p2 => decide (p1 = p2)
  | _, _ => false

def r3_unconditional_counterexample_endpoint_exec_bracket_eq_bool : Bool :=
  match Reidemeister.r3BraidLeft r3UnconditionalCounterexampleGraph 0 2 4,
      Reidemeister.r3BraidRight r3UnconditionalCounterexampleGraph 0 2 4 with
  | .ok gL, .ok gR => execBracketEqBool gL gR
  | _, _ => false

theorem r3_unconditional_counterexample_endpoint_exec_bracket_eq_fails :
    r3_unconditional_counterexample_endpoint_exec_bracket_eq_bool = false := by
  native_decide

end HeytingLean.Tests.Topology.KauffmanR3NegativeTargets
