import HeytingLean.LeanCP.VCG.SWPSound

/-!
# LeanCP Bounded State-Sensitive While Rules

`swp` already handles the full non-loop fragment. This module adds a bounded
state-sensitive while-rule surface indexed by an iteration budget.

The current rule is intentionally scoped to `NoReturn` loop bodies. A
one-continuation `swp` cannot distinguish normal completion from a body that
returns `CVal.undef`, so early-return loops require a richer continuation type.
-/

namespace HeytingLean.LeanCP

/-- Fuel used to execute a loop body of depth `stmtDepth body` for at most
`iters` truthy iterations, plus the final exit check. -/
def swhileFuel (body : CStmt) (iters : Nat) : Nat :=
  stmtDepth body + iters + 1

/-- Bounded state-sensitive while-rule. The index counts the remaining truthy
iterations allowed before the rule gives up. -/
noncomputable def swhileWP : Nat → CExpr → SProp → CStmt → (CVal → SProp) → SProp
  | 0, cond, inv, _body, Q => fun st =>
      inv st ∧
        match evalExpr cond st with
        | some v => if isTruthy v then False else Q CVal.undef st
        | none => False
  | iters + 1, cond, inv, body, Q => fun st =>
      inv st ∧
        match evalExpr cond st with
        | some v =>
            if isTruthy v then
              swp body (fun _ => swhileWP iters cond inv body Q) st
            else
              Q CVal.undef st
        | none => False

theorem swhileWP_sound (cond : CExpr) (inv : SProp) (ann : HProp) (body : CStmt)
    (hloop : LoopFree body) (hnr : NoReturn body) :
    ∀ {iters Q st},
      swhileWP iters cond inv body Q st →
      ∃ st', execStmt (swhileFuel body iters) (.whileInv cond ann body) st = some (.normal st') ∧
        Q CVal.undef st' := by
  intro iters
  induction iters with
  | zero =>
      intro Q st hwp
      rcases hwp with ⟨_hinv, hstep⟩
      cases hcond : evalExpr cond st with
      | none =>
          simp [hcond] at hstep
      | some v =>
          cases htruth : isTruthy v with
          | true =>
              simp [hcond, htruth] at hstep
          | false =>
              refine ⟨st, ?_, ?_⟩
              · change execStmt (Nat.succ (stmtDepth body)) (.whileInv cond ann body) st =
                  some (.normal st)
                simp [execStmt, hcond, htruth]
              · simpa [swhileWP, hcond, htruth] using hstep
  | succ iters ih =>
      intro Q st hwp
      rcases hwp with ⟨_hinv, hstep⟩
      cases hcond : evalExpr cond st with
      | none =>
          simp [hcond] at hstep
      | some v =>
          cases htruth : isTruthy v with
          | true =>
              have hbody : swp body (fun _ => swhileWP iters cond inv body Q) st := by
                simpa [swhileWP, hcond, htruth] using hstep
              have hfuel :
                  stmtDepth body ≤ stmtDepth body + iters + 1 := by
                calc
                  stmtDepth body ≤ stmtDepth body + (iters + 1) := Nat.le_add_right _ _
                  _ = stmtDepth body + iters + 1 := by simp [Nat.add_assoc]
              rcases swp_sound_normal body hloop hnr hfuel hbody with ⟨st', hexecBody, hcont⟩
              rcases ih hcont with ⟨st'', hexecLoop, hq⟩
              refine ⟨st'', ?_, hq⟩
              change execStmt (Nat.succ (stmtDepth body + iters + 1)) (.whileInv cond ann body) st =
                some (.normal st'')
              simp [execStmt, hcond, htruth, hexecBody]
              simpa [swhileFuel, execStmt, Nat.add_assoc] using hexecLoop
          | false =>
              refine ⟨st, ?_, ?_⟩
              · change execStmt (Nat.succ (stmtDepth body + iters + 1)) (.whileInv cond ann body) st =
                  some (.normal st)
                simp [execStmt, hcond, htruth]
              · simpa [swhileWP, hcond, htruth] using hstep

end HeytingLean.LeanCP
