import HeytingLean.LoF.ICC.YFree

namespace HeytingLean
namespace LoF
namespace ICC

/--
The honest Phase 1 soundness surface is the closed Y-free fragment.

This file proves preservation for the four principal ICC rewrite rules on closed
Y-free terms. It does not claim global consistency or unrestricted-`Y`
soundness.
-/
def ClosedYFree (t : Term) : Prop :=
  Term.Closed t ∧ YFree t

theorem closedAbove_mono {k m : Nat} {t : Term}
    (hkm : k ≤ m) (h : Term.closedAbove k t) : Term.closedAbove m t := by
  induction t generalizing k m with
  | var idx =>
      simpa [Term.closedAbove] using Nat.lt_of_lt_of_le h hkm
  | lam body ih =>
      simp [Term.closedAbove] at h ⊢
      exact ih (Nat.succ_le_succ hkm) h
  | app fn arg ihFn ihArg =>
      rcases h with ⟨hFn, hArg⟩
      exact ⟨ihFn hkm hFn, ihArg hkm hArg⟩
  | bridge body ih =>
      simp [Term.closedAbove] at h ⊢
      exact ih (Nat.succ_le_succ hkm) h
  | ann val typ ihVal ihTyp =>
      rcases h with ⟨hVal, hTyp⟩
      exact ⟨ihVal hkm hVal, ihTyp hkm hTyp⟩

theorem substAt_preserves_closedAbove :
    ∀ {cutoff : Nat} {repl t : Term},
      Term.closedAbove (cutoff + 1) t →
      Term.Closed repl →
      Term.closedAbove cutoff (Term.substAt cutoff repl t)
  | cutoff, repl, .var idx, hBody, hRepl => by
      have hLe : idx ≤ cutoff := Nat.lt_succ_iff.mp hBody
      by_cases hEq : idx = cutoff
      · subst hEq
        have hRepl' : Term.closedAbove idx repl := closedAbove_mono (Nat.zero_le _) hRepl
        have hShift : Term.shiftAbove repl 0 idx = repl := by
          simpa [Term.Closed] using (Term.shiftAbove_closedAbove_eq (k := 0) (inc := idx) hRepl)
        simpa [Term.closedAbove, Term.substAt, hShift] using hRepl'
      · have hNotLt : ¬ cutoff < idx := Nat.not_lt_of_ge hLe
        have hLt : idx < cutoff := Nat.lt_of_le_of_ne hLe hEq
        simpa [Term.closedAbove, Term.substAt, hEq, hNotLt] using hLt
  | cutoff, repl, .lam body, hBody, hRepl => by
      simpa [Term.closedAbove, Term.substAt] using
        (substAt_preserves_closedAbove
          (cutoff := cutoff + 1) (repl := repl) (t := body) hBody hRepl)
  | cutoff, repl, .app fn arg, hBody, hRepl => by
      rcases hBody with ⟨hFn, hArg⟩
      exact ⟨
        substAt_preserves_closedAbove (cutoff := cutoff) (repl := repl) (t := fn) hFn hRepl,
        substAt_preserves_closedAbove (cutoff := cutoff) (repl := repl) (t := arg) hArg hRepl
      ⟩
  | cutoff, repl, .bridge body, hBody, hRepl => by
      simpa [Term.closedAbove, Term.substAt] using
        (substAt_preserves_closedAbove
          (cutoff := cutoff + 1) (repl := repl) (t := body) hBody hRepl)
  | cutoff, repl, .ann val typ, hBody, hRepl => by
      rcases hBody with ⟨hVal, hTyp⟩
      exact ⟨
        substAt_preserves_closedAbove (cutoff := cutoff) (repl := repl) (t := val) hVal hRepl,
        substAt_preserves_closedAbove (cutoff := cutoff) (repl := repl) (t := typ) hTyp hRepl
      ⟩

private theorem closed_ne_var_zero {t : Term} (hClosed : Term.Closed t) :
    t ≠ .var 0 := by
  intro hEq
  subst hEq
  simp [Term.Closed, Term.closedAbove] at hClosed

private theorem closed_ne_ann_seed {t : Term} (hClosed : Term.Closed t) :
    t ≠ .ann (.var 0) (.var 0) := by
  intro hEq
  subst hEq
  simp [Term.Closed, Term.closedAbove] at hClosed

private theorem substAt_succ_eq_var_zero :
    ∀ {cutoff : Nat} {repl t : Term},
      Term.Closed repl →
      Term.substAt (cutoff + 1) repl t = .var 0 →
      t = .var 0
  | cutoff, repl, .var idx, hReplClosed, h => by
      by_cases hEq : idx = cutoff + 1
      · have hShift : Term.shiftAbove repl 0 (cutoff + 1) = repl := by
          simpa [Term.Closed] using
            (Term.shiftAbove_closedAbove_eq (k := 0) (inc := cutoff + 1) hReplClosed)
        simp [Term.substAt, hEq, hShift] at h
        exact False.elim ((closed_ne_var_zero hReplClosed) h)
      · by_cases hLt : cutoff + 1 < idx
        · simp [Term.substAt, hEq, hLt] at h
          exfalso
          omega
        · simp [Term.substAt, hEq, hLt] at h
          subst idx
          rfl
  | cutoff, repl, .lam body, hReplClosed, h => by
      simp [Term.substAt] at h
  | cutoff, repl, .app fn arg, hReplClosed, h => by
      simp [Term.substAt] at h
  | cutoff, repl, .bridge body, hReplClosed, h => by
      simp [Term.substAt] at h
  | cutoff, repl, .ann val typ, hReplClosed, h => by
      simp [Term.substAt] at h

private theorem substAt_succ_eq_ann_seed :
    ∀ {cutoff : Nat} {repl t : Term},
      Term.Closed repl →
      Term.substAt (cutoff + 1) repl t = .ann (.var 0) (.var 0) →
      t = .ann (.var 0) (.var 0)
  | cutoff, repl, .var idx, hReplClosed, h => by
      by_cases hEq : idx = cutoff + 1
      · have hShift : Term.shiftAbove repl 0 (cutoff + 1) = repl := by
          simpa [Term.Closed] using
            (Term.shiftAbove_closedAbove_eq (k := 0) (inc := cutoff + 1) hReplClosed)
        simp [Term.substAt, hEq, hShift] at h
        exact False.elim ((closed_ne_ann_seed hReplClosed) h)
      · by_cases hLt : cutoff + 1 < idx
        · simp [Term.substAt, hEq, hLt] at h
        · simp [Term.substAt, hEq, hLt] at h
  | cutoff, repl, .lam body, hReplClosed, h => by
      simp [Term.substAt] at h
  | cutoff, repl, .app fn arg, hReplClosed, h => by
      simp [Term.substAt] at h
  | cutoff, repl, .bridge body, hReplClosed, h => by
      simp [Term.substAt] at h
  | cutoff, repl, .ann val typ, hReplClosed, h => by
      simp [Term.substAt] at h
      rcases h with ⟨hVal, hTyp⟩
      have hValEq : val = .var 0 := substAt_succ_eq_var_zero hReplClosed hVal
      have hTypEq : typ = .var 0 := substAt_succ_eq_var_zero hReplClosed hTyp
      simp [hValEq, hTypEq]

private theorem substAt_preserves_noLegacy :
    ∀ {cutoff : Nat} {repl t : Term},
      Term.closedAbove (cutoff + 1) t →
      Term.Closed repl →
      YFree repl →
      containsLegacyYShim t = false →
      containsLegacyYShim (Term.substAt cutoff repl t) = false
  | cutoff, repl, .var idx, hBody, hReplClosed, hRepl, _ => by
      have hLe : idx ≤ cutoff := Nat.lt_succ_iff.mp hBody
      by_cases hEq : idx = cutoff
      · subst hEq
        have hShift : Term.shiftAbove repl 0 idx = repl := by
          simpa [Term.Closed] using (Term.shiftAbove_closedAbove_eq (k := 0) (inc := idx) hReplClosed)
        simpa [YFree, isYFree, Term.substAt, hShift] using hRepl
      · have hNotLt : ¬ cutoff < idx := Nat.not_lt_of_ge hLe
        simp [Term.substAt, hEq, hNotLt, containsLegacyYShim]
  | cutoff, repl, .lam body, hBody, hReplClosed, hRepl, hNo => by
      simpa [Term.substAt, containsLegacyYShim] using
        (substAt_preserves_noLegacy
          (cutoff := cutoff + 1) (repl := repl) (t := body) hBody hReplClosed hRepl hNo)
  | cutoff, repl, .app fn arg, hBody, hReplClosed, hRepl, hNo => by
      rcases hBody with ⟨hFnClosed, hArgClosed⟩
      have hParts : containsLegacyYShim fn = false ∧ containsLegacyYShim arg = false := by
        simpa [containsLegacyYShim, Bool.or_eq_false_iff] using hNo
      have hFn' :=
        substAt_preserves_noLegacy
          (cutoff := cutoff) (repl := repl) (t := fn) hFnClosed hReplClosed hRepl hParts.1
      have hArg' :=
        substAt_preserves_noLegacy
          (cutoff := cutoff) (repl := repl) (t := arg) hArgClosed hReplClosed hRepl hParts.2
      simpa [Term.substAt, containsLegacyYShim, Bool.or_eq_false_iff] using And.intro hFn' hArg'
  | cutoff, repl, .bridge body, hBody, hReplClosed, hRepl, hNo => by
      have hBridgeNe : (.bridge body) ≠ legacyY := by
        intro hEq
        simp [containsLegacyYShim, legacyY, hEq] at hNo
      have hBodyNo : containsLegacyYShim body = false := by
        simpa [containsLegacyYShim, hBridgeNe] using hNo
      have hBody' :=
        substAt_preserves_noLegacy
          (cutoff := cutoff + 1) (repl := repl) (t := body) hBody hReplClosed hRepl hBodyNo
      by_cases hSeed : (.bridge (Term.substAt (cutoff + 1) repl body)) = legacyY
      · have hInner : Term.substAt (cutoff + 1) repl body = .ann (.var 0) (.var 0) := by
          injection hSeed with hInner
        have hBodyEq : body = .ann (.var 0) (.var 0) := substAt_succ_eq_ann_seed hReplClosed hInner
        exact False.elim (hBridgeNe (by simp [legacyY, hBodyEq]))
      · simp [Term.substAt, containsLegacyYShim, hSeed, hBody']
  | cutoff, repl, .ann val typ, hBody, hReplClosed, hRepl, hNo => by
      rcases hBody with ⟨hValClosed, hTypClosed⟩
      have hParts : containsLegacyYShim val = false ∧ containsLegacyYShim typ = false := by
        simpa [containsLegacyYShim, Bool.or_eq_false_iff] using hNo
      have hVal' :=
        substAt_preserves_noLegacy
          (cutoff := cutoff) (repl := repl) (t := val) hValClosed hReplClosed hRepl hParts.1
      have hTyp' :=
        substAt_preserves_noLegacy
          (cutoff := cutoff) (repl := repl) (t := typ) hTypClosed hReplClosed hRepl hParts.2
      simpa [Term.substAt, containsLegacyYShim, Bool.or_eq_false_iff] using And.intro hVal' hTyp'

theorem substAt_preserves_yFree {cutoff : Nat} {repl t : Term}
    (hBody : Term.closedAbove (cutoff + 1) t)
    (hReplClosed : Term.Closed repl)
    (hRepl : YFree repl)
    (h : YFree t) :
    YFree (Term.substAt cutoff repl t) := by
  have hNo : containsLegacyYShim t = false := by
    simpa [YFree, isYFree] using h
  have hOut :
      containsLegacyYShim (Term.substAt cutoff repl t) = false :=
    substAt_preserves_noLegacy hBody hReplClosed hRepl hNo
  simpa [YFree, isYFree] using hOut

theorem beta_preserves_closedYFree {body arg : Term}
    (hClosed : Term.Closed (.app (.lam body) arg))
    (hY : YFree (.app (.lam body) arg)) :
    ClosedYFree (Term.subst0 arg body) := by
  have hClosedParts : Term.closedAbove 1 body ∧ Term.Closed arg := by
    simpa [Term.Closed, Term.closedAbove] using hClosed
  have hYParts : YFree body ∧ YFree arg := by
    have hRaw :
        containsLegacyYShim body = false ∧ containsLegacyYShim arg = false := by
      simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using hY
    exact ⟨by simpa [YFree, isYFree] using hRaw.1, by simpa [YFree, isYFree] using hRaw.2⟩
  constructor
  · simpa [Term.subst0] using
      substAt_preserves_closedAbove (cutoff := 0) hClosedParts.1 hClosedParts.2
  · simpa [Term.subst0] using
      substAt_preserves_yFree (cutoff := 0) hClosedParts.1 hClosedParts.2 hYParts.2 hYParts.1

theorem app_bridge_preserves_closedYFree {body arg : Term}
    (hClosed : Term.Closed (.app (.bridge body) arg))
    (hY : YFree (.app (.bridge body) arg)) :
    ClosedYFree (.bridge (.app body (.ann (.var 0) (arg.shift 1)))) := by
  have hClosedParts : Term.closedAbove 1 body ∧ Term.Closed arg := by
    simpa [Term.Closed, Term.closedAbove] using hClosed
  have hBridgeNe : (.bridge body) ≠ legacyY := by
    have hRaw : containsLegacyYShim (.bridge body) = false := by
      simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using (And.left (show
        containsLegacyYShim (.bridge body) = false ∧ containsLegacyYShim arg = false by
          simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using hY))
    intro hEq
    simp [containsLegacyYShim, legacyY, hEq] at hRaw
  have hBodyNo : containsLegacyYShim body = false := by
    have hRaw : containsLegacyYShim (.bridge body) = false := by
      simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using (And.left (show
        containsLegacyYShim (.bridge body) = false ∧ containsLegacyYShim arg = false by
          simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using hY))
    simpa [containsLegacyYShim, hBridgeNe] using hRaw
  have hArgNo : containsLegacyYShim arg = false := by
    simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using (And.right (show
      containsLegacyYShim (.bridge body) = false ∧ containsLegacyYShim arg = false by
        simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using hY))
  constructor
  · have hArg1 : Term.closedAbove 1 arg := closedAbove_mono (Nat.zero_le _) hClosedParts.2
    have hArgShiftEq : arg.shift 1 = arg := by
      simpa [Term.shift] using (Term.shift_closed hClosedParts.2 1)
    have hArgShift1 : Term.closedAbove 1 (arg.shift 1) := by
      simpa [hArgShiftEq] using hArg1
    exact ⟨hClosedParts.1, ⟨by simp [Term.closedAbove], hArgShift1⟩⟩
  · have hBodyY : YFree body := by simpa [YFree, isYFree] using hBodyNo
    have hArgY : YFree arg := by simpa [YFree, isYFree] using hArgNo
    have hArgShiftEq : arg.shift 1 = arg := by
      simpa [Term.shift] using (Term.shift_closed hClosedParts.2 1)
    have hShiftArgY : YFree (arg.shift 1) := by
      simpa [hArgShiftEq] using hArgY
    have hBodyNo' : containsLegacyYShim body = false := by simpa [YFree, isYFree] using hBodyY
    have hShiftArgNo : containsLegacyYShim (arg.shift 1) = false := by
      simpa [YFree, isYFree] using hShiftArgY
    have hOutNe : (.bridge (.app body (.ann (.var 0) (arg.shift 1)))) ≠ legacyY := by
      simp [legacyY]
    simp [YFree, isYFree, containsLegacyYShim, hOutNe, hBodyNo', hShiftArgNo]

theorem ann_lam_preserves_closedYFree {val body : Term}
    (hClosed : Term.Closed (.ann val (.lam body)))
    (hY : YFree (.ann val (.lam body))) :
    ClosedYFree (.lam (.ann (.app (val.shift 1) (.var 0)) (Term.subst0 (.bridge (.var 0)) body))) := by
  have hClosedParts : Term.Closed val ∧ Term.closedAbove 1 body := by
    simpa [Term.Closed, Term.closedAbove] using hClosed
  have hYParts : YFree val ∧ YFree body := by
    have hRaw :
        containsLegacyYShim val = false ∧ containsLegacyYShim body = false := by
      simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using hY
    exact ⟨by simpa [YFree, isYFree] using hRaw.1, by simpa [YFree, isYFree] using hRaw.2⟩
  have hBridgeVarClosed : Term.Closed (.bridge (.var 0)) := by
    simp [Term.Closed, Term.closedAbove]
  have hBridgeVarY : YFree (.bridge (.var 0)) := by
    simp [YFree, isYFree, containsLegacyYShim, legacyY]
  constructor
  · have hVal1 : Term.closedAbove 1 val := closedAbove_mono (Nat.zero_le _) hClosedParts.1
    have hValShiftEq : val.shift 1 = val := by
      simpa [Term.shift] using (Term.shift_closed hClosedParts.1 1)
    have hSubst : Term.closedAbove 0 (Term.subst0 (.bridge (.var 0)) body) := by
      simpa [Term.subst0] using
        substAt_preserves_closedAbove (cutoff := 0) hClosedParts.2 hBridgeVarClosed
    have hValShift1 : Term.closedAbove 1 (val.shift 1) := by
      simpa [hValShiftEq] using hVal1
    have hSubst1 : Term.closedAbove 1 (Term.subst0 (.bridge (.var 0)) body) :=
      closedAbove_mono (Nat.zero_le _) hSubst
    exact ⟨⟨hValShift1, by simp [Term.closedAbove]⟩, hSubst1⟩
  · have hSubst : YFree (Term.subst0 (.bridge (.var 0)) body) := by
      simpa [Term.subst0] using
        substAt_preserves_yFree (cutoff := 0) hClosedParts.2 hBridgeVarClosed hBridgeVarY hYParts.2
    have hValShiftEq : val.shift 1 = val := by
      simpa [Term.shift] using (Term.shift_closed hClosedParts.1 1)
    have hShiftValY : YFree (val.shift 1) := by
      simpa [hValShiftEq] using hYParts.1
    have hShiftValNo : containsLegacyYShim (val.shift 1) = false := by
      simpa [YFree, isYFree] using hShiftValY
    have hSubstNo : containsLegacyYShim (Term.subst0 (.bridge (.var 0)) body) = false := by
      simpa [YFree, isYFree] using hSubst
    simp [YFree, isYFree, containsLegacyYShim, hShiftValNo, hSubstNo]

theorem ann_bridge_preserves_closedYFree {val body : Term}
    (hClosed : Term.Closed (.ann val (.bridge body)))
    (hY : YFree (.ann val (.bridge body))) :
    ClosedYFree (Term.subst0 val body) := by
  have hClosedParts : Term.Closed val ∧ Term.closedAbove 1 body := by
    simpa [Term.Closed, Term.closedAbove] using hClosed
  have hValNo : containsLegacyYShim val = false := by
    simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using
      (show containsLegacyYShim val = false ∧ containsLegacyYShim (.bridge body) = false by
        simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using hY).1
  have hBridgeNo : containsLegacyYShim (.bridge body) = false := by
    simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using
      (show containsLegacyYShim val = false ∧ containsLegacyYShim (.bridge body) = false by
        simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using hY).2
  have hBridgeNe : (.bridge body) ≠ legacyY := by
    intro hEq
    simp [containsLegacyYShim, legacyY, hEq] at hBridgeNo
  have hBodyNo : containsLegacyYShim body = false := by
    simpa [containsLegacyYShim, hBridgeNe] using hBridgeNo
  have hValY : YFree val := by simpa [YFree, isYFree] using hValNo
  have hBodyY : YFree body := by simpa [YFree, isYFree] using hBodyNo
  constructor
  · simpa [Term.subst0] using
      substAt_preserves_closedAbove (cutoff := 0) hClosedParts.2 hClosedParts.1
  · simpa [Term.subst0] using
      substAt_preserves_yFree (cutoff := 0) hClosedParts.2 hClosedParts.1 hValY hBodyY

private theorem yFree_app_parts {fn arg : Term} (h : YFree (.app fn arg)) :
    YFree fn ∧ YFree arg := by
  have hRaw : containsLegacyYShim fn = false ∧ containsLegacyYShim arg = false := by
    simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using h
  exact ⟨by simpa [YFree, isYFree] using hRaw.1, by simpa [YFree, isYFree] using hRaw.2⟩

private theorem yFree_ann_parts {val typ : Term} (h : YFree (.ann val typ)) :
    YFree val ∧ YFree typ := by
  have hRaw : containsLegacyYShim val = false ∧ containsLegacyYShim typ = false := by
    simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using h
  exact ⟨by simpa [YFree, isYFree] using hRaw.1, by simpa [YFree, isYFree] using hRaw.2⟩

theorem step_preserves_closedYFree {t u : Term} (hStep : Step t u) :
    ClosedYFree t → ClosedYFree u := by
  intro h
  induction hStep with
  | beta body arg =>
      exact beta_preserves_closedYFree h.1 h.2
  | app_bridge body arg =>
      exact app_bridge_preserves_closedYFree h.1 h.2
  | ann_lam val body =>
      exact ann_lam_preserves_closedYFree h.1 h.2
  | ann_bridge val body =>
      exact ann_bridge_preserves_closedYFree h.1 h.2
  | legacy_y arg =>
      have hNo : containsLegacyYShim legacyY = false := by
        simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using
          (show containsLegacyYShim legacyY = false ∧ containsLegacyYShim arg = false by
            simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using h.2).1
      simp [containsLegacyYShim_legacyY] at hNo
  | app_left hs ih =>
      rename_i fn fn' arg
      have hClosedParts : Term.Closed fn ∧ Term.Closed arg := by
        simpa [Term.Closed, Term.closedAbove] using h.1
      have hYParts : YFree fn ∧ YFree arg := yFree_app_parts h.2
      have hFn' : ClosedYFree fn' := ih ⟨hClosedParts.1, hYParts.1⟩
      constructor
      · simpa [Term.Closed, Term.closedAbove] using And.intro hFn'.1 hClosedParts.2
      · have hFnNo : containsLegacyYShim fn' = false := by
          simpa [YFree, isYFree] using hFn'.2
        have hArgNo : containsLegacyYShim arg = false := by
          simpa [YFree, isYFree] using hYParts.2
        simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using And.intro hFnNo hArgNo
  | app_right hs ih =>
      rename_i fn arg arg'
      have hClosedParts : Term.Closed fn ∧ Term.Closed arg := by
        simpa [Term.Closed, Term.closedAbove] using h.1
      have hYParts : YFree fn ∧ YFree arg := yFree_app_parts h.2
      have hArg' : ClosedYFree arg' := ih ⟨hClosedParts.2, hYParts.2⟩
      constructor
      · simpa [Term.Closed, Term.closedAbove] using And.intro hClosedParts.1 hArg'.1
      · have hFnNo : containsLegacyYShim fn = false := by
          simpa [YFree, isYFree] using hYParts.1
        have hArgNo : containsLegacyYShim arg' = false := by
          simpa [YFree, isYFree] using hArg'.2
        simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using And.intro hFnNo hArgNo
  | ann_left hs ih =>
      rename_i val val' typ
      have hClosedParts : Term.Closed val ∧ Term.Closed typ := by
        simpa [Term.Closed, Term.closedAbove] using h.1
      have hYParts : YFree val ∧ YFree typ := yFree_ann_parts h.2
      have hVal' : ClosedYFree val' := ih ⟨hClosedParts.1, hYParts.1⟩
      constructor
      · simpa [Term.Closed, Term.closedAbove] using And.intro hVal'.1 hClosedParts.2
      · have hValNo : containsLegacyYShim val' = false := by
          simpa [YFree, isYFree] using hVal'.2
        have hTypNo : containsLegacyYShim typ = false := by
          simpa [YFree, isYFree] using hYParts.2
        simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using And.intro hValNo hTypNo
  | ann_right hs ih =>
      rename_i val typ typ'
      have hClosedParts : Term.Closed val ∧ Term.Closed typ := by
        simpa [Term.Closed, Term.closedAbove] using h.1
      have hYParts : YFree val ∧ YFree typ := yFree_ann_parts h.2
      have hTyp' : ClosedYFree typ' := ih ⟨hClosedParts.2, hYParts.2⟩
      constructor
      · simpa [Term.Closed, Term.closedAbove] using And.intro hClosedParts.1 hTyp'.1
      · have hValNo : containsLegacyYShim val = false := by
          simpa [YFree, isYFree] using hYParts.1
        have hTypNo : containsLegacyYShim typ' = false := by
          simpa [YFree, isYFree] using hTyp'.2
        simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using And.intro hValNo hTypNo

theorem step_preserves_yFree {t u : Term}
    (hStep : Step t u) (hClosed : Term.Closed t) (hY : YFree t) : YFree u :=
  (step_preserves_closedYFree hStep ⟨hClosed, hY⟩).2

theorem steps_preserve_closedYFree {t u : Term} (hSteps : Steps t u) :
    ClosedYFree t → ClosedYFree u := by
  intro h
  induction hSteps with
  | refl _ =>
      exact h
  | trans hs hrest ih =>
      exact ih (step_preserves_closedYFree hs h)

theorem steps_preserve_yFree {t u : Term}
    (hSteps : Steps t u) (hClosed : Term.Closed t) (hY : YFree t) : YFree u :=
  (steps_preserve_closedYFree hSteps ⟨hClosed, hY⟩).2

private theorem app_of_closedYFree {fn arg : Term}
    (hFn : ClosedYFree fn) (hArg : ClosedYFree arg) : ClosedYFree (.app fn arg) := by
  constructor
  · simpa [Term.Closed, Term.closedAbove] using And.intro hFn.1 hArg.1
  · have hFnNo : containsLegacyYShim fn = false := by
      simpa [YFree, isYFree] using hFn.2
    have hArgNo : containsLegacyYShim arg = false := by
      simpa [YFree, isYFree] using hArg.2
    simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using And.intro hFnNo hArgNo

private theorem ann_of_closedYFree {val typ : Term}
    (hVal : ClosedYFree val) (hTyp : ClosedYFree typ) : ClosedYFree (.ann val typ) := by
  constructor
  · simpa [Term.Closed, Term.closedAbove] using And.intro hVal.1 hTyp.1
  · have hValNo : containsLegacyYShim val = false := by
      simpa [YFree, isYFree] using hVal.2
    have hTypNo : containsLegacyYShim typ = false := by
      simpa [YFree, isYFree] using hTyp.2
    simpa [YFree, isYFree, containsLegacyYShim, Bool.or_eq_false_iff] using And.intro hValNo hTypNo

theorem step?_preserves_closedYFree :
    ∀ {t u : Term}, step? t = some u → ClosedYFree t → ClosedYFree u := by
  intro t
  induction t with
  | var idx =>
      intro u h
      simp [step?] at h
  | lam body ih =>
      intro u h
      simp [step?] at h
  | bridge body ih =>
      intro u h
      simp [step?] at h
  | app fn arg ihFn ihArg =>
      intro u h hClosedY
      cases fn with
      | var idx =>
          have hClosedParts : Term.Closed (.var idx) ∧ Term.Closed arg := by
            simpa [Term.Closed, Term.closedAbove] using hClosedY.1
          have hYParts : YFree (.var idx) ∧ YFree arg := yFree_app_parts hClosedY.2
          cases hArg : step? arg <;> simp [step?, hArg] at h
          case some arg' =>
            cases h
            exact app_of_closedYFree ⟨hClosedParts.1, hYParts.1⟩
              (ihArg hArg ⟨hClosedParts.2, hYParts.2⟩)
      | lam body =>
          cases h
          exact beta_preserves_closedYFree hClosedY.1 hClosedY.2
      | app fn₁ arg₁ =>
          have hClosedParts : Term.Closed (.app fn₁ arg₁) ∧ Term.Closed arg := by
            simpa [Term.Closed, Term.closedAbove] using hClosedY.1
          have hYParts : YFree (.app fn₁ arg₁) ∧ YFree arg := yFree_app_parts hClosedY.2
          cases hFn : step? (.app fn₁ arg₁) <;> simp [step?, hFn] at h
          case some fn' =>
            cases h
            exact app_of_closedYFree (ihFn hFn ⟨hClosedParts.1, hYParts.1⟩) ⟨hClosedParts.2, hYParts.2⟩
          case none =>
            cases hArg : step? arg <;> simp [hArg] at h
            case some arg' =>
              cases h
              exact app_of_closedYFree ⟨hClosedParts.1, hYParts.1⟩ (ihArg hArg ⟨hClosedParts.2, hYParts.2⟩)
      | bridge body =>
          cases body with
          | ann val typ =>
              cases val with
              | var valIdx =>
                  cases typ with
                  | var typIdx =>
                      cases valIdx with
                      | zero =>
                          cases typIdx with
                          | zero =>
                              have hParts : YFree legacyY ∧ YFree arg := by
                                simpa [legacyY] using yFree_app_parts hClosedY.2
                              have hNo : containsLegacyYShim legacyY = false := by
                                simpa [YFree, isYFree] using hParts.1
                              simp [containsLegacyYShim_legacyY] at hNo
                          | succ _ =>
                              replace h := by simpa [step?] using h
                              cases h
                              exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
                      | succ _ =>
                          replace h := by simpa [step?] using h
                          cases h
                          exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
                  | lam _ =>
                      replace h := by simpa [step?] using h
                      cases h
                      exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
                  | app _ _ =>
                      replace h := by simpa [step?] using h
                      cases h
                      exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
                  | bridge _ =>
                      replace h := by simpa [step?] using h
                      cases h
                      exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
                  | ann _ _ =>
                      replace h := by simpa [step?] using h
                      cases h
                      exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
              | lam _ =>
                  cases h
                  exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
              | app _ _ =>
                  cases h
                  exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
              | bridge _ =>
                  cases h
                  exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
              | ann _ _ =>
                  cases h
                  exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
          | var _ =>
              cases h
              exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
          | lam _ =>
              cases h
              exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
          | app _ _ =>
              cases h
              exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
          | bridge _ =>
              cases h
              exact app_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
      | ann val typ =>
          have hClosedParts : Term.Closed (.ann val typ) ∧ Term.Closed arg := by
            simpa [Term.Closed, Term.closedAbove] using hClosedY.1
          have hYParts : YFree (.ann val typ) ∧ YFree arg := yFree_app_parts hClosedY.2
          cases hFn : step? (.ann val typ) <;> simp [step?, hFn] at h
          case some fn' =>
            cases h
            exact app_of_closedYFree (ihFn hFn ⟨hClosedParts.1, hYParts.1⟩) ⟨hClosedParts.2, hYParts.2⟩
          case none =>
            cases hArg : step? arg <;> simp [hArg] at h
            case some arg' =>
              cases h
              exact app_of_closedYFree ⟨hClosedParts.1, hYParts.1⟩ (ihArg hArg ⟨hClosedParts.2, hYParts.2⟩)
  | ann val typ ihVal ihTyp =>
      intro u h hClosedY
      cases typ with
      | lam body =>
          cases h
          exact ann_lam_preserves_closedYFree hClosedY.1 hClosedY.2
      | bridge body =>
          cases h
          exact ann_bridge_preserves_closedYFree hClosedY.1 hClosedY.2
      | var idx =>
          have hClosedParts : Term.Closed val ∧ Term.Closed (.var idx) := by
            simpa [Term.Closed, Term.closedAbove] using hClosedY.1
          have hYParts : YFree val ∧ YFree (.var idx) := yFree_ann_parts hClosedY.2
          cases hVal : step? val <;> simp [step?, hVal] at h
          case some val' =>
            cases h
            exact ann_of_closedYFree (ihVal hVal ⟨hClosedParts.1, hYParts.1⟩)
              ⟨hClosedParts.2, hYParts.2⟩
      | app fn arg =>
          have hClosedParts : Term.Closed val ∧ Term.Closed (.app fn arg) := by
            simpa [Term.Closed, Term.closedAbove] using hClosedY.1
          have hYParts : YFree val ∧ YFree (.app fn arg) := yFree_ann_parts hClosedY.2
          cases hVal : step? val <;> simp [step?, hVal] at h
          case some val' =>
            cases h
            exact ann_of_closedYFree (ihVal hVal ⟨hClosedParts.1, hYParts.1⟩)
              ⟨hClosedParts.2, hYParts.2⟩
          case none =>
            cases hTyp : step? (.app fn arg) <;> simp [hTyp] at h
            case some typ' =>
              cases h
              exact ann_of_closedYFree ⟨hClosedParts.1, hYParts.1⟩
                (ihTyp hTyp ⟨hClosedParts.2, hYParts.2⟩)
      | ann val' typ' =>
          have hClosedParts : Term.Closed val ∧ Term.Closed (.ann val' typ') := by
            simpa [Term.Closed, Term.closedAbove] using hClosedY.1
          have hYParts : YFree val ∧ YFree (.ann val' typ') := yFree_ann_parts hClosedY.2
          cases hVal : step? val <;> simp [step?, hVal] at h
          case some val'' =>
            cases h
            exact ann_of_closedYFree (ihVal hVal ⟨hClosedParts.1, hYParts.1⟩)
              ⟨hClosedParts.2, hYParts.2⟩
          case none =>
            cases hTyp : step? (.ann val' typ') <;> simp [hTyp] at h
            case some typ'' =>
              cases h
              exact ann_of_closedYFree ⟨hClosedParts.1, hYParts.1⟩
                (ihTyp hTyp ⟨hClosedParts.2, hYParts.2⟩)

theorem reduceFuel_preserves_closedYFree (fuel : Nat) {t : Term}
    (hClosed : Term.Closed t) (hY : YFree t) : ClosedYFree (reduceFuel fuel t) := by
  induction fuel generalizing t with
  | zero =>
      simpa [reduceFuel] using And.intro hClosed hY
  | succ n ih =>
      cases hStep : step? t with
      | none =>
          simpa [reduceFuel, hStep] using And.intro hClosed hY
      | some u =>
          have hNext : ClosedYFree u := step?_preserves_closedYFree hStep ⟨hClosed, hY⟩
          simpa [reduceFuel, hStep] using ih (t := u) hNext.1 hNext.2

theorem reduceFuel_preserves_yFree (fuel : Nat) {t : Term}
    (hClosed : Term.Closed t) (hY : YFree t) : YFree (reduceFuel fuel t) :=
  (reduceFuel_preserves_closedYFree fuel hClosed hY).2

theorem checkYFree_operational_sound {fuel : Nat} {t : Term}
    (hClosed : Term.Closed t) (hCheck : checkYFree fuel t = true) :
    ClosedYFree t ∧
      step? (reduceFuel fuel t) = none ∧
      ∀ {u : Term}, Steps t u → ClosedYFree u := by
  have hBase := checkYFree_sound (fuel := fuel) (t := t) hCheck
  refine ⟨⟨hClosed, hBase.1⟩, hBase.2, ?_⟩
  intro u hSteps
  exact steps_preserve_closedYFree hSteps ⟨hClosed, hBase.1⟩

end ICC
end LoF
end HeytingLean
