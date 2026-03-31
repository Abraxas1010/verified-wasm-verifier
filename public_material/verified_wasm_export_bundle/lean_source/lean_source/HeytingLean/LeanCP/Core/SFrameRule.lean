import HeytingLean.LeanCP.VCG.SWP
import HeytingLean.LeanCP.Core.StateSepLog

namespace HeytingLean.LeanCP

/-- Expressions whose evaluation is independent of the heap. -/
def HeapIndependentExpr : CExpr → Prop
  | .var _ => True
  | .intLit _ => True
  | .floatLit _ => True
  | .null => True
  | .sizeOf _ => True
  | .cast _ e => HeapIndependentExpr e
  | .addrOf _ => True
  | .binop _ e1 e2 => HeapIndependentExpr e1 ∧ HeapIndependentExpr e2
  | .deref _ => False
  | .arrayAccess _ _ => False
  | .fieldAccess _ _ => False
  | .call _ _ => False

/-- Fragment of `swp` that is stable under framing by heap-only state assertions. -/
def SFrameSafe : CStmt → Prop
  | .skip => True
  | .decl _ _ => True
  | .assign (.var _) e => HeapIndependentExpr e
  | .assign _ _ => False
  | .seq s1 s2 => SFrameSafe s1 ∧ SFrameSafe s2
  | .ite cond th el => HeapIndependentExpr cond ∧ SFrameSafe th ∧ SFrameSafe el
  | .ret e => HeapIndependentExpr e
  | .block _ _ => False
  | .switch _ _ _ _ => False
  | .forLoop _ _ _ _ => False
  | .break => False
  | .continue => False
  | .whileInv _ _ _ => False
  | .alloc _ _ => False
  | .free _ _ => False

@[simp] theorem ofHProp_updateVar (P : HProp) (st : CState) (x : String) (v : CVal) :
    SProp.ofHProp P (st.updateVar x v) ↔ SProp.ofHProp P st := by
  rfl

@[simp] theorem updateVar_setHeap (st : CState) (h : Heap) (x : String) (v : CVal) :
    ({ st with heap := h }).updateVar x v = { st.updateVar x v with heap := h } := by
  cases st
  rfl

theorem evalExpr_heapIndependent :
    ∀ (e : CExpr), HeapIndependentExpr e → ∀ (st : CState) (h : Heap),
      evalExpr e { st with heap := h } = evalExpr e st
  | .var _, _, _, _ =>
      by simp [evalExpr, evalStaticExpr, CState.lookupVar]
  | .intLit _, _, _, _ =>
      by simp [evalExpr, evalStaticExpr]
  | .floatLit _, _, _, _ =>
      by simp [evalExpr, evalStaticExpr]
  | .null, _, _, _ =>
      by simp [evalExpr, evalStaticExpr]
  | .sizeOf _, _, _, _ =>
      by simp [evalExpr, evalStaticExpr]
  | .cast ty e, he, st, h =>
      by
        simp [evalExpr, evalStaticExpr, evalExpr_heapIndependent e he st h]
  | .binop op e1 e2, ⟨he1, he2⟩, st, h =>
      by
        cases op <;>
          try simp [evalExpr, evalStaticExpr,
            evalExpr_heapIndependent e1 he1 st h,
            evalExpr_heapIndependent e2 he2 st h]
        all_goals rfl
  | .deref _, hfalse, _, _ =>
      False.elim hfalse
  | .addrOf _, _, _, _ =>
      by simp [evalExpr, evalStaticExpr]
  | .arrayAccess _ _, hfalse, _, _ =>
      False.elim hfalse
  | .fieldAccess _ _, hfalse, _, _ =>
      False.elim hfalse
  | .call _ _, hfalse, _, _ =>
      False.elim hfalse

theorem swp_mono (s : CStmt) (Q Q' : CVal → SProp)
    (hpost : ∀ v, Q v ⊢ₛₛ Q' v) :
    swp s Q ⊢ₛₛ swp s Q' := by
  revert Q Q'
  induction s with
  | skip =>
      intro Q Q' hpost
      exact hpost CVal.undef
  | ret e =>
      intro Q Q' hpost st
      cases h : evalExpr e st with
      | none =>
          simp [swp, h]
      | some v =>
          simpa [swp, h] using hpost v st
  | decl x ty =>
      intro Q Q' hpost st
      simpa [swp] using hpost CVal.undef (st.updateVar x CVal.undef)
  | block decls body ih =>
      intro Q Q' hpost st
      have hpost' :
          ∀ v,
            (fun st' => Q v (restoreBlockState st st' decls)) ⊢ₛₛ
            (fun st' => Q' v (restoreBlockState st st' decls)) := by
        intro v st' hq
        exact hpost v _ hq
      simpa [swp] using
        ih
          (fun v st' => Q v (restoreBlockState st st' decls))
          (fun v st' => Q' v (restoreBlockState st st' decls))
          hpost'
          (enterBlockState st decls)
  | switch e tag caseBody default =>
      intro Q Q' hpost st
      simp [swp]
  | forLoop init cond step body =>
      intro Q Q' hpost st
      simp [swp]
  | «break» =>
      intro Q Q' hpost st
      simp [swp]
  | «continue» =>
      intro Q Q' hpost st
      simp [swp]
  | assign lhs rhs =>
      intro Q Q' hpost st
      cases lhs with
      | var x =>
          cases h : evalExpr rhs st with
          | none =>
              simp [swp, h]
          | some v =>
              simpa [swp, h] using hpost CVal.undef (st.updateVar x v)
      | deref p =>
          cases hp : evalExpr p st with
          | none =>
              simp [swp, hp]
          | some pv =>
              cases pv with
              | int n =>
                  simp [swp, hp]
              | uint n sz =>
                  simp [swp, hp]
              | float v =>
                  simp [swp, hp]
              | null =>
                  simp [swp, hp]
              | undef =>
                  simp [swp, hp]
              | structVal fields =>
                  simp [swp, hp]
              | unionVal tag inner =>
                  simp [swp, hp]
              | ptr block offset =>
                  cases hrhs : evalExpr rhs st with
                  | none =>
                      simp [swp, hp, hrhs]
                  | some v =>
                      simpa [swp, hp, hrhs] using
                        (show ((∃ vOld, st.readPtr { block := block, offset := offset } = some vOld) ∧
                            ∃ st', st.writePtr { block := block, offset := offset } v = some st' ∧
                              Q CVal.undef st') →
                            ((∃ vOld, st.readPtr { block := block, offset := offset } = some vOld) ∧
                              ∃ st', st.writePtr { block := block, offset := offset } v = some st' ∧
                                Q' CVal.undef st') from
                          fun hpair =>
                            let ⟨hOld, st', hwrite, hq⟩ := hpair
                            ⟨hOld, st', hwrite, hpost CVal.undef _ hq⟩)
      | fieldAccess p field =>
          cases hp : evalExpr p st with
          | none =>
              simp [swp, hp]
          | some pv =>
              cases pv with
              | int n =>
                  simp [swp, hp]
              | uint n sz =>
                  simp [swp, hp]
              | float v =>
                  simp [swp, hp]
              | null =>
                  simp [swp, hp]
              | undef =>
                  simp [swp, hp]
              | structVal fields =>
                  simp [swp, hp]
              | unionVal tag inner =>
                  simp [swp, hp]
              | ptr block offset =>
                  cases hrhs : evalExpr rhs st with
                  | none =>
                      simp [swp, hp, hrhs]
                  | some v =>
                      simpa [swp, hp, hrhs] using
                        (show (∃ slot vOld st',
                            PtrVal.addOffset { block := block, offset := offset }
                              (Int.ofNat (fieldOffset field)) = some slot ∧
                            st.readPtr slot = some vOld ∧
                            st.writePtr slot v = some st' ∧
                            Q CVal.undef st') →
                            (∃ slot vOld st',
                              PtrVal.addOffset { block := block, offset := offset }
                                (Int.ofNat (fieldOffset field)) = some slot ∧
                              st.readPtr slot = some vOld ∧
                              st.writePtr slot v = some st' ∧
                              Q' CVal.undef st') from
                          fun hpair =>
                            let ⟨slot, hOld, st', hslot, hread, hwrite, hq⟩ := hpair
                            ⟨slot, hOld, st', hslot, hread, hwrite, hpost CVal.undef _ hq⟩)
      | intLit n =>
          simp [swp]
      | floatLit v =>
          simp [swp]
      | null =>
          simp [swp]
      | sizeOf ty =>
          simp [swp]
      | cast ty e =>
          simp [swp]
      | binop op e1 e2 =>
          simp [swp]
      | addrOf x =>
          simp [swp]
      | arrayAccess arr idx =>
          simp [swp]
      | call fn args =>
          simp [swp]
  | seq s1 s2 ih1 ih2 =>
      intro Q Q' hpost
      exact ih1 _ _ (fun _ => ih2 _ _ hpost)
  | ite cond th el ihTh ihEl =>
      intro Q Q' hpost st
      cases hcond : evalExpr cond st with
      | none =>
          simp [swp, hcond]
      | some v =>
          cases htruth : isTruthy v with
          | false =>
              simpa [swp, hcond, htruth] using ihEl Q Q' hpost st
          | true =>
              simpa [swp, hcond, htruth] using ihTh Q Q' hpost st
  | whileInv cond inv body ih =>
      intro Q Q' hpost st h
      rcases h with ⟨hinv, hbody, hexit⟩
      refine ⟨hinv, hbody, ?_⟩
      intro st' hinv'
      exact hpost CVal.undef st' (hexit st' hinv')
  | alloc x cells =>
      intro Q Q' hpost st
      simpa [swp] using hpost CVal.undef (st.allocCells x cells)
  | free e cells =>
      intro Q Q' hpost st
      cases hEval : evalExpr e st with
      | none =>
          simp [swp, hEval]
      | some v =>
          cases v with
          | int n =>
              simp [swp, hEval]
          | uint n sz =>
              simp [swp, hEval]
          | float v =>
              simp [swp, hEval]
          | null =>
              simp [swp, hEval]
          | undef =>
              simp [swp, hEval]
          | structVal fields =>
              simp [swp, hEval]
          | unionVal tag inner =>
              simp [swp, hEval]
          | ptr block offset =>
              simpa [swp, hEval] using
                (show (∃ flatAddr, st.resolvePtr { block := block, offset := offset } = some flatAddr ∧
                    Q CVal.undef (st.freeCells flatAddr cells)) →
                    (∃ flatAddr, st.resolvePtr { block := block, offset := offset } = some flatAddr ∧
                      Q' CVal.undef (st.freeCells flatAddr cells)) from
                  fun hpair =>
                    let ⟨flatAddr, hresolve, hq⟩ := hpair
                    ⟨flatAddr, hresolve, hpost CVal.undef _ hq⟩)

/-- State-level frame rule for the env-only fragment of `swp`. The frame is a
lifted heap assertion, so it is stable under the variable updates performed by
`decl` and variable assignment. -/
theorem swp_frame (body : CStmt) (hsafe : SFrameSafe body) (Q : CVal → SProp) (R : HProp) :
    (swp body Q ∗ₛ SProp.ofHProp R) ⊢ₛₛ swp body (fun v => Q v ∗ₛ SProp.ofHProp R) := by
  revert hsafe Q R
  induction body with
  | skip =>
      intro _ Q R st h
      simpa [swp] using h
  | block decls body ih =>
      intro hs Q R
      cases hs
  | switch e tag caseBody default =>
      intro hs Q R
      cases hs
  | forLoop init cond step body =>
      intro hs Q R
      cases hs
  | «break» =>
      intro hs Q R
      cases hs
  | «continue» =>
      intro hs Q R
      cases hs
  | ret e =>
      intro he Q R st h
      rcases h with ⟨h1, h2, hdis, hEq, hwp, hR⟩
      cases hEval1 : evalExpr e { st with heap := h1 } with
      | none =>
          simp [swp, hEval1] at hwp
      | some v =>
          have hEval : evalExpr e st = some v := by
            simpa [evalExpr_heapIndependent e he st h1] using hEval1
          have hq : Q v { st with heap := h1 } := by
            simpa [swp, hEval1] using hwp
          have hframed : (Q v ∗ₛ SProp.ofHProp R) st := ⟨h1, h2, hdis, hEq, hq, hR⟩
          simpa [swp, hEval] using hframed
  | decl x ty =>
      intro _ Q R st h
      rcases h with ⟨h1, h2, hdis, hEq, hwp, hR⟩
      have hq : Q CVal.undef (({ st with heap := h1 }).updateVar x CVal.undef) := by
        simpa [swp] using hwp
      change (Q CVal.undef ∗ₛ SProp.ofHProp R) (st.updateVar x CVal.undef)
      refine ⟨h1, h2, hdis, ?_, ?_, ?_⟩
      · simpa [hEq]
      · simpa using hq
      · simpa using hR
  | assign lhs rhs =>
      intro hs Q R st h
      cases lhs with
      | var x =>
          rcases h with ⟨h1, h2, hdis, hEq, hwp, hR⟩
          cases hEval1 : evalExpr rhs { st with heap := h1 } with
          | none =>
              simp [swp, hEval1] at hwp
          | some v =>
              have hEval : evalExpr rhs st = some v := by
                simpa [evalExpr_heapIndependent rhs hs st h1] using hEval1
              have hq : Q CVal.undef (({ st with heap := h1 }).updateVar x v) := by
                simpa [swp, hEval1] using hwp
              have hframed : (Q CVal.undef ∗ₛ SProp.ofHProp R) (st.updateVar x v) := by
                refine ⟨h1, h2, hdis, ?_, ?_, ?_⟩
                · simpa [hEq]
                · simpa using hq
                · simpa using hR
              simpa [swp, hEval] using hframed
      | deref p =>
          cases hs
      | fieldAccess p field =>
          cases hs
      | intLit n =>
          cases hs
      | floatLit v =>
          cases hs
      | null =>
          cases hs
      | sizeOf ty =>
          cases hs
      | cast ty e =>
          cases hs
      | binop op e1 e2 =>
          cases hs
      | addrOf x =>
          cases hs
      | arrayAccess arr idx =>
          cases hs
      | call fn args =>
          cases hs
  | seq s1 s2 ih1 ih2 =>
      intro hs Q R
      rcases hs with ⟨hs1, hs2⟩
      exact StateSepLog.sentails_trans _ _ _
        (ih1 hs1 _ _)
        (swp_mono s1 _ _ (fun _ => ih2 hs2 _ _))
  | ite cond th el ihTh ihEl =>
      intro hs Q R st h
      rcases hs with ⟨hcondSafe, hsTh, hsEl⟩
      rcases h with ⟨h1, h2, hdis, hEq, hwp, hR⟩
      cases hEval1 : evalExpr cond { st with heap := h1 } with
      | none =>
          simp [swp, hEval1] at hwp
      | some v =>
          have hEval : evalExpr cond st = some v := by
            simpa [evalExpr_heapIndependent cond hcondSafe st h1] using hEval1
          cases htruth : isTruthy v with
          | false =>
              have hbranch : swp el Q { st with heap := h1 } := by
                simpa [swp, hEval1, htruth] using hwp
              have hframed : swp el (fun v => Q v ∗ₛ SProp.ofHProp R) st := by
                exact ihEl hsEl _ _ _ ⟨h1, h2, hdis, hEq, hbranch, hR⟩
              simpa [swp, hEval, htruth] using hframed
          | true =>
              have hbranch : swp th Q { st with heap := h1 } := by
                simpa [swp, hEval1, htruth] using hwp
              have hframed : swp th (fun v => Q v ∗ₛ SProp.ofHProp R) st := by
                exact ihTh hsTh _ _ _ ⟨h1, h2, hdis, hEq, hbranch, hR⟩
              simpa [swp, hEval, htruth] using hframed
  | whileInv cond inv body ih =>
      intro hs Q R
      cases hs
  | alloc x cells =>
      intro hs Q R
      cases hs
  | free e cells =>
      intro hs Q R
      cases hs

end HeytingLean.LeanCP
