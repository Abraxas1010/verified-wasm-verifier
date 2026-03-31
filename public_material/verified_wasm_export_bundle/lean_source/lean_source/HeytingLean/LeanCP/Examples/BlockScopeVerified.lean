import HeytingLean.LeanCP.VCG.SWPSound
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Tactics.Forward

/-!
# LeanCP Example: Verified Block Scope

This is the first end-to-end consumer of the Phase 4 block-scoping surface. The
spec requires `tmp` to be absent before entry and proves that it is absent again
after the block returns, while the returned value is still the arithmetic sum.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

private theorem filter_eq_self_of_lookup_none (env : Env) (x : String)
    (hlookup : List.lookup x env = none) :
    env.filter (fun p => p.1 != x) = env := by
  induction env with
  | nil =>
      simp
  | cons head tail ih =>
      rcases head with ⟨y, v⟩
      cases hxy : (x == y) with
      | true =>
          simp [List.lookup, hxy] at hlookup
      | false =>
          have hyxNe : y ≠ x := by
            intro hyxEq
            subst y
            simp at hxy
          have hyxKeep : (y != x) = true := by
            simpa [bne_iff_ne] using hyxNe
          have htail : List.lookup x tail = none := by
            simpa [List.lookup, hxy] using hlookup
          simp [List.filter, hyxKeep, ih htail]

private theorem removeVar_updateVar_cancel (st : CState) (x : String) (v : CVal)
    (hlookup : st.lookupVar x = none) :
    (st.updateVar x v).removeVar x = st := by
  cases st with
  | mk heap env nextAddr =>
      have hfilter : env.filter (fun p => p.1 != x) = env :=
        filter_eq_self_of_lookup_none env x hlookup
      simp [CState.updateVar, CState.removeVar, hfilter]

private theorem removeVar_after_updateVar (st : CState) (x : String) (v : CVal) :
    (st.updateVar x v).removeVar x = st.removeVar x := by
  cases st with
  | mk heap env nextAddr =>
      simp [CState.updateVar, CState.removeVar]

def blockAddProgram : CStmt :=
  .block [("tmp", .int)]
    (.seq
      (.assign (.var "tmp") (.binop .add (.var "a") (.var "b")))
      (.ret (.var "tmp")))

def blockAddSpec (a b : Int) : SFunSpec where
  name := "block_add"
  params := [("a", .int), ("b", .int)]
  retType := .int
  pre := fun st =>
    st.lookupVar "a" = some (.int a) ∧
    st.lookupVar "b" = some (.int b) ∧
    st.lookupVar "tmp" = none
  post := fun ret st =>
    ret = .int (a + b) ∧
    st.lookupVar "a" = some (.int a) ∧
    st.lookupVar "b" = some (.int b) ∧
    st.lookupVar "tmp" = none
  body := blockAddProgram

private theorem blockAdd_loopFree : LoopFree blockAddProgram := by
  simp [blockAddProgram, LoopFree]

private theorem blockAdd_tailReturn : TailReturn blockAddProgram := by
  simp [blockAddProgram, TailReturn, NoReturn]

theorem blockAdd_verified (a b : Int) :
    sgenVC (blockAddSpec a b) := by
  intro st hpre
  rcases hpre with ⟨ha, hb, htmp⟩
  let entry := enterBlockState st [("tmp", .int)]
  let st1 := entry.updateVar "tmp" (.int (a + b))
  have hatmp : "a" ≠ "tmp" := by decide
  have hbtmp : "b" ≠ "tmp" := by decide
  have haEntry : entry.lookupVar "a" = some (.int a) := by
    calc
      entry.lookupVar "a" = st.lookupVar "a" := by
        simpa [entry, enterBlockState] using
          lookupVar_updateVar_ne st "tmp" "a" CVal.undef hatmp
      _ = some (.int a) := ha
  have hbEntry : entry.lookupVar "b" = some (.int b) := by
    calc
      entry.lookupVar "b" = st.lookupVar "b" := by
        simpa [entry, enterBlockState] using
          lookupVar_updateVar_ne st "tmp" "b" CVal.undef hbtmp
      _ = some (.int b) := hb
  have hEvalAdd :
      evalExpr (.binop .add (.var "a") (.var "b")) entry = some (.int (a + b)) := by
    simpa [evalExpr, evalStaticExpr, haEntry, hbEntry] using
      (show evalBinOp .add (.int a) (.int b) = some (.int (a + b)) by
        rfl)
  have hEvalTmp : evalExpr (.var "tmp") st1 = some (.int (a + b)) := by
    simp [st1, CState.lookupVar, CState.updateVar]
  have hRestore : restoreBlockState st st1 [("tmp", .int)] = st := by
    calc
      restoreBlockState st st1 [("tmp", .int)] = st1.removeVar "tmp" := by
        simp [restoreBlockState, htmp]
      _ = entry.removeVar "tmp" := by
        simpa [st1] using removeVar_after_updateVar entry "tmp" (.int (a + b))
      _ = st := by
        simpa [entry, enterBlockState] using removeVar_updateVar_cancel st "tmp" CVal.undef htmp
  have hpost :
      (blockAddSpec a b).post (.int (a + b)) (restoreBlockState st st1 [("tmp", .int)]) := by
    rw [hRestore]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · exact ha
    · exact hb
    · exact htmp
  change swp blockAddProgram (blockAddSpec a b).post st
  simp [blockAddProgram, swp, entry, st1, hEvalAdd, hEvalTmp, hpost]

theorem blockAdd_executes (a b : Int) {st fuel}
    (hpre : (blockAddSpec a b).pre st)
    (hfuel : stmtDepth blockAddProgram ≤ fuel) :
    ∃ res, execStmt fuel blockAddProgram st = some res ∧
      match res with
      | .returned ret st' => (blockAddSpec a b).post ret st'
      | .normal st' => (blockAddSpec a b).post CVal.undef st' := by
  have hvc : swp blockAddProgram (blockAddSpec a b).post st :=
    blockAdd_verified a b st hpre
  exact swp_sound blockAddProgram blockAdd_loopFree blockAdd_tailReturn hfuel hvc

end HeytingLean.LeanCP.Examples
