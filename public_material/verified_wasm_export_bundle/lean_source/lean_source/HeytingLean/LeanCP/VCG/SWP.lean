import HeytingLean.LeanCP.VCG.SFunSpec

/-!
# LeanCP State-Sensitive Weakest Preconditions

State-sensitive weakest preconditions aligned with the full `execStmt`
operational semantics.
-/

namespace HeytingLean.LeanCP

/-- State-sensitive weakest precondition. Normal completion threads `CVal.undef`. -/
noncomputable def swp : CStmt → (CVal → SProp) → SProp
  | .skip, Q => Q CVal.undef
  | .ret e, Q => fun st =>
      match evalExpr e st with
      | some v => Q v st
      | none => False
  | .block decls body, Q => fun st =>
      swp body (fun ret st' => Q ret (restoreBlockState st st' decls)) (enterBlockState st decls)
  | .switch _ _ _ _, _ => fun _ => False
  | .forLoop _ _ _ _, _ => fun _ => False
  | .break, _ => fun _ => False
  | .continue, _ => fun _ => False
  | .decl x _, Q => fun st =>
      Q CVal.undef (st.updateVar x CVal.undef)
  | .assign (.var x) e, Q => fun st =>
      match evalExpr e st with
      | some v => Q CVal.undef (st.updateVar x v)
      | none => False
  | .assign (.deref p) e, Q => fun st =>
      match evalExpr p st, evalExpr e st with
      | some (.ptr block offset), some v =>
          let addr : PtrVal := { block := block, offset := offset }
          (∃ vOld, st.readPtr addr = some vOld) ∧
          ∃ st', st.writePtr addr v = some st' ∧ Q CVal.undef st'
      | _, _ => False
  | .assign (.fieldAccess p field) e, Q => fun st =>
      match evalExpr p st, evalExpr e st with
      | some (.ptr block offset), some v =>
          let addr : PtrVal := { block := block, offset := offset }
          ∃ slot vOld st',
            PtrVal.addOffset addr (Int.ofNat (fieldOffset field)) = some slot ∧
            st.readPtr slot = some vOld ∧
            st.writePtr slot v = some st' ∧
            Q CVal.undef st'
      | _, _ => False
  | .seq s1 s2, Q =>
      swp s1 (fun _ => swp s2 Q)
  | .ite cond th el, Q => fun st =>
      match evalExpr cond st with
      | some v => if isTruthy v then swp th Q st else swp el Q st
      | none => False
  | .alloc x cells, Q => fun st =>
      Q CVal.undef (st.allocCells x cells)
  | .free e cells, Q => fun st =>
      match evalExpr e st with
      | some (.ptr block offset) =>
          let addr : PtrVal := { block := block, offset := offset }
          ∃ flatAddr,
            st.resolvePtr addr = some flatAddr ∧
            Q CVal.undef (st.freeCells flatAddr cells)
      | _ => False
  | .whileInv _cond inv body, Q => fun st =>
      SProp.ofHProp inv st ∧
        (∀ st', SProp.ofHProp inv st' → swp body (fun _ => SProp.ofHProp inv) st') ∧
        (∀ st', SProp.ofHProp inv st' → Q CVal.undef st')
  | .assign _ _, _ => fun _ => False

/-- State-sensitive verification-condition generator. -/
def sgenVC (spec : SFunSpec) : Prop :=
  ∀ st, spec.pre st → swp spec.body spec.post st

/-- Mem-post compatibility surface for the existing state-sensitive `swp`.
This is honest because `swp` only requires `SProp` in the post position; we can
therefore lift arbitrary `MemHProp` posts through `SProp.ofMemHProp` even
though loop invariants remain heap-only in the current AST. -/
def swpMemPost (s : CStmt) (Q : CVal → MemHProp) : SProp :=
  swp s (fun v => SProp.ofMemHProp (Q v))

@[simp] theorem swpMemPost_onMem (s : CStmt) (Q : CVal → HProp) :
    swpMemPost s (fun v => (Q v).onMem) = swp s (fun v => SProp.ofHProp (Q v)) := by
  funext st
  simp [swpMemPost, SProp.ofHProp_eq_ofMemHProp_onMem]

end HeytingLean.LeanCP
