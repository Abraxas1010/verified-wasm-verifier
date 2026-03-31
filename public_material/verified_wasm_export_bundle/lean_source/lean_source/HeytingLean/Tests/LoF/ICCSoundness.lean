import HeytingLean.LoF.ICC.Soundness
import HeytingLean.LoF.ICC.Workloads

open HeytingLean.LoF.ICC

example : ClosedYFree (embedLegacy (.app .S .K)) := by
  constructor
  · exact closed_embedLegacy (.app .S .K)
  · simpa [YFree] using (show isYFree (embedLegacy (.app .S .K)) = true by native_decide)

example : containsLegacyYShim HeytingLean.LoF.ICC.sampleTerm = true := by
  native_decide

example :
    Steps (embedLegacy (.app (.app .K .S) .K)) (embedLegacy .S) := by
  simpa [embedLegacy] using k_rule_steps .S .K

example :
    ClosedYFree (Term.subst0 (embedLegacy .K) (.lam (.var 1))) := by
  simpa [ClosedYFree, subst0_k_body] using
    beta_preserves_closedYFree
      (body := .lam (.var 1))
      (arg := embedLegacy .K)
      (by simp [Term.Closed, Term.closedAbove])
      (by
        simpa [YFree] using
          (show isYFree (.app (.lam (.var 1)) (embedLegacy .K)) = true by native_decide))

example : ClosedYFree (reduceFuel 1 (.app (.lam (.var 0)) kTerm)) := by
  have hClosed : Term.Closed (.app (.lam (.var 0)) kTerm) := by
    simp [Term.Closed, Term.closedAbove]
  have hY : YFree (.app (.lam (.var 0)) kTerm) := by
    simpa [YFree] using
      (show isYFree (.app (.lam (.var 0)) kTerm) = true by native_decide)
  simpa [reduceFuel, step?, Term.subst0, Term.substAt] using
    reduceFuel_preserves_closedYFree 1 hClosed hY

example {u : Term} (hSteps : Steps (embedLegacy (.app .S .K)) u) :
    ClosedYFree u := by
  have hOperational :=
    checkYFree_operational_sound
      (fuel := 8)
      (t := embedLegacy (.app .S .K))
      (closed_embedLegacy (.app .S .K))
      (by native_decide)
  exact hOperational.2.2 hSteps
