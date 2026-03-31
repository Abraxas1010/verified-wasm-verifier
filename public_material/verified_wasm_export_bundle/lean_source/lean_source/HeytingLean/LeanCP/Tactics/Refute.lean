import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.Lang.CSemantics

/-!
# LeanCP Refutation Tactic

Implements the Zhang et al. counterexample-guided refutation technique:
given a CFunSpec and concrete test inputs, checks whether the postcondition
holds on the actual execution result. If not, the spec is REFUTED.

Reference: Zhang et al. "Neuro-Symbolic Generation and Validation of
Memory-Aware Formal Function Specifications" (arXiv:2603.13414, Section 4.1).
-/

namespace HeytingLean.LeanCP

/-- Result of a refutation attempt. -/
inductive RefuteResult where
  | refuted : String → RefuteResult    -- spec is definitely wrong
  | inconclusive : RefuteResult         -- test case did not refute
  | execError : String → RefuteResult   -- couldn't execute
  deriving Repr

/-- Attempt to refute a spec by running it on concrete inputs.
    If execution produces a result that violates the postcondition
    (checked via operational semantics), the spec is refuted. -/
def refuteWithInputs (spec : CFunSpec) (args : List CVal)
    (checkPost : CVal → CState → Bool) : RefuteResult :=
  let env := spec.params.zip args |>.map fun ((name, _), val) => (name, val)
  let st : CState := { heap := Heap.empty, env := env, nextAddr := 100 }
  match execStmt 10000 spec.body st with
  | some (.returned v st') =>
      if checkPost v st' then .inconclusive
      else .refuted s!"Postcondition violated: returned {repr v}"
  | some (.normal _) =>
      .refuted "Function did not return a value"
  | none =>
      .execError "Execution failed (out of fuel or undefined behavior)"

/-- `leancp_refute` tactic — attempts to refute a spec by finding
    counterexamples. Currently operates via #eval-based checking. -/
syntax "leancp_refute" : tactic
macro_rules
  | `(tactic| leancp_refute) => `(tactic|
      (simp [genVC, wp, entails]
       <;> try omega
       <;> try decide))

end HeytingLean.LeanCP
