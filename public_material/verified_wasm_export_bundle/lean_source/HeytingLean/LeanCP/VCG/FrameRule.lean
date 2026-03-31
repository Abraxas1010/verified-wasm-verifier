import HeytingLean.LeanCP.VCG.WP

/-!
# LeanCP Frame Rule Automation

This module proves the WP frame rule on the fragment whose clauses are actually
frame-stable under LeanCP's current heap-only assertion language. `whileInv`
is excluded: its invariant is an assertion over the whole heap, so the naive
statement "frame any `R` through any while" is false without stronger invariant
stability hypotheses or a richer state-sensitive assertion layer.
-/

namespace HeytingLean.LeanCP

/-- Statements whose current WP clauses are frame-stable. -/
def FrameSafe : CStmt → Prop
  | .skip => True
  | .ret _ => True
  | .assign _ _ => True
  | .seq s1 s2 => FrameSafe s1 ∧ FrameSafe s2
  | .ite _ thenBr elseBr => FrameSafe thenBr ∧ FrameSafe elseBr
  | .block _ body => FrameSafe body
  | .switch _ _ _ _ => False
  | .forLoop _ _ _ _ => False
  | .break => False
  | .continue => False
  | .whileInv _ _ _ => False
  | .alloc _ _ => True
  | .free _ _ => True
  | .decl _ _ => True

/-- Frame a magic wand by preserving an extra disjoint heap fragment. -/
theorem wand_frame (P Q R : HProp) :
    ((P -∗ Q) ∗ R) ⊢ₛ (P -∗ (Q ∗ R)) := by
  intro h hsplit h' hdis' hP
  rcases hsplit with ⟨h1, h2, hdis12, hEq, hwand, hR⟩
  have hdisUnion : Finmap.Disjoint (Heap.union h1 h2) h' := by
    simpa [hEq] using hdis'
  have hparts := (Finmap.disjoint_union_left h1 h2 h').mp hdisUnion
  have hQ : Q (Heap.union h1 h') := hwand h' hparts.1 hP
  have hdisQR : Finmap.Disjoint (Heap.union h1 h') h2 := by
    simpa [Heap.union] using
      (Finmap.disjoint_union_left h1 h' h2).2 ⟨hdis12, Heap.disjoint_comm.mpr hparts.2⟩
  refine ⟨Heap.union h1 h', h2, hdisQR, ?_, hQ, hR⟩
  calc
    Heap.union h h'
        = Heap.union (Heap.union h1 h2) h' := by simp [hEq]
    _ = Heap.union h1 (Heap.union h2 h') := by
          simp [Heap.union, Finmap.union_assoc]
    _ = Heap.union h1 (Heap.union h' h2) := by
          rw [Heap.union_comm_of_disjoint hparts.2]
    _ = Heap.union (Heap.union h1 h') h2 := by
          simp [Heap.union, Finmap.union_assoc]

/-- WP is monotone in its postcondition: if Q entails Q' pointwise,
    then wp s Q entails wp s Q'. Proved by structural induction on s. -/
theorem wp_mono (s : CStmt) (Q Q' : CVal → HProp)
    (hpost : ∀ v, Q v ⊢ₛ Q' v) : wp s Q ⊢ₛ wp s Q' := by
  revert Q Q'
  induction s with
  | skip =>
    intro Q Q' hpost
    exact hpost CVal.undef
  | ret e =>
    intro Q Q' hpost
    cases h : evalStaticExpr e with
    | none =>
      simpa [wp, h] using hpost CVal.undef
    | some v =>
      simpa [wp, h] using hpost v
  | block decls body ih =>
    intro Q Q' hpost
    simpa [wp] using ih Q Q' hpost
  | switch e tag caseBody default ihCase ihDefault =>
    intro Q Q' hpost
    cases h : evalStaticExpr e with
    | none =>
      intro hheap hswitch
      simpa [wp, h] using hswitch
    | some v =>
      cases v with
      | int n =>
        by_cases htag : n = tag
        · simpa [wp, h, htag] using ihCase Q Q' hpost
        · simpa [wp, h, htag] using ihDefault Q Q' hpost
      | uint _ _ =>
        intro hheap hswitch
        simpa [wp, h] using hswitch
      | ptr _ _ =>
        intro hheap hswitch
        simpa [wp, h] using hswitch
      | structVal _ =>
        intro hheap hswitch
        simpa [wp, h] using hswitch
      | unionVal _ _ =>
        intro hheap hswitch
        simpa [wp, h] using hswitch
      | null =>
        intro hheap hswitch
        simpa [wp, h] using hswitch
      | undef =>
        intro hheap hswitch
        simpa [wp, h] using hswitch
      | float _ =>
        intro hheap hswitch
        simpa [wp, h] using hswitch
  | forLoop init cond step body ihInit ihStep ihBody =>
    intro Q Q' hpost
    exact SepLog.entails_refl _
  | «break» =>
    intro Q Q' hpost
    exact SepLog.entails_refl _
  | «continue» =>
    intro Q Q' hpost
    exact SepLog.entails_refl _
  | assign lhs rhs =>
    intro Q Q' hpost
    cases lhs with
    | var x =>
      cases h : evalStaticExpr rhs with
      | none =>
        simpa [wp, h] using hpost CVal.undef
      | some v =>
        simpa [wp, h] using hpost v
    | deref p =>
      intro h ⟨addr, vOld, vNew, h1, h2, hdis, hEq, hstore, hwand⟩
      exact ⟨addr, vOld, vNew, h1, h2, hdis, hEq, hstore,
        fun h' hdis' hstore' => hpost CVal.undef _ (hwand h' hdis' hstore')⟩
    | fieldAccess p field =>
      intro h ⟨addr, vOld, vNew, h1, h2, hdis, hEq, hstore, hwand⟩
      exact ⟨addr, vOld, vNew, h1, h2, hdis, hEq, hstore,
        fun h' hdis' hstore' => hpost CVal.undef _ (hwand h' hdis' hstore')⟩
    | _ =>
      simpa [wp] using hpost CVal.undef
  | seq s1 s2 ih1 ih2 =>
    intro Q Q' hpost
    exact ih1 _ _ (fun _ => ih2 _ _ hpost)
  | ite cond thenBr elseBr ihThen ihElse =>
    intro Q Q' hpost
    cases h : evalStaticExpr cond with
    | none =>
      intro hheap hcond
      have hcond' : HProp.hand (wp thenBr Q) (wp elseBr Q) hheap := by
        simpa [wp, h] using hcond
      rcases hcond' with ⟨hThen, hElse⟩
      simpa [wp, h] using
        (show HProp.hand (wp thenBr Q') (wp elseBr Q') hheap from
          ⟨ihThen _ _ hpost _ hThen, ihElse _ _ hpost _ hElse⟩)
    | some v =>
      by_cases hv : isTruthy v
      · simpa [wp, h, hv] using ihThen Q Q' hpost
      · simpa [wp, h, hv] using ihElse Q Q' hpost
  | whileInv cond inv body ih =>
    intro Q Q' hpost h ⟨hinv, hpure⟩
    rcases hpure with ⟨hemp, hclauses⟩
    rcases hclauses with ⟨hbody, hexit⟩
    exact ⟨hinv, ⟨hemp, ⟨fun h' hinv' =>
      ih _ _ (fun _ => SepLog.entails_refl _) _ (hbody h' hinv'),
      fun h' hinv' => hpost CVal.undef _ (hexit h' hinv')⟩⟩⟩
  | alloc x cells =>
    intro Q Q' hpost h ⟨addr, hwand⟩
    exact ⟨addr, fun h' hdis hblock => hpost (.ptr 0 (Int.ofNat addr)) _ (hwand h' hdis hblock)⟩
  | free e cells =>
    intro Q Q' hpost
    cases e with
    | var x =>
      intro h ⟨addr, vs, hlen, hblock⟩
      rcases hblock with ⟨h1, h2, hdis, hEq, hvals, hwand⟩
      exact ⟨addr, vs, hlen, ⟨h1, h2, hdis, hEq, hvals,
        fun h' hdis' hemp => hpost CVal.undef _ (hwand h' hdis' hemp)⟩⟩
    | _ =>
      simpa [wp] using hpost CVal.undef
  | decl _ _ =>
    intro Q Q' hpost
    exact hpost CVal.undef

/-- Consequence rule: weaken precondition, strengthen postcondition. -/
theorem wp_consequence (s : CStmt) (P P' : HProp) (Q Q' : CVal → HProp)
    (hpre : P' ⊢ₛ P) (hpost : ∀ v, Q v ⊢ₛ Q' v)
    (hwp : P ⊢ₛ wp s Q) : P' ⊢ₛ wp s Q' :=
  SepLog.entails_trans P' (wp s Q) (wp s Q')
    (SepLog.entails_trans P' P (wp s Q) hpre hwp)
    (wp_mono s Q Q' hpost)

/-- Frame rule for the fragment whose current WP clauses are actually frame-safe. -/
theorem wp_frame (s : CStmt) (hs : FrameSafe s) (Q : CVal → HProp) (R : HProp) :
    (wp s Q ∗ R) ⊢ₛ wp s (fun v => Q v ∗ R) := by
  revert Q R hs
  induction s with
  | skip =>
    intro _ Q R
    exact SepLog.entails_refl _
  | ret e =>
    intro _ Q R
    cases h : evalStaticExpr e with
    | none =>
      simpa [wp, h] using (SepLog.entails_refl ((Q CVal.undef) ∗ R))
    | some v =>
      simpa [wp, h] using (SepLog.entails_refl ((Q v) ∗ R))
  | block decls body ih =>
    intro hs Q R
    simpa [wp] using ih hs Q R
  | switch e tag caseBody default ihCase ihDefault =>
    intro hs Q R
    cases hs
  | forLoop init cond step body ihInit ihStep ihBody =>
    intro hs Q R
    cases hs
  | «break» =>
    intro hs Q R
    cases hs
  | «continue» =>
    intro hs Q R
    cases hs
  | assign lhs rhs =>
    intro _ Q R
    cases lhs with
    | var x =>
      cases h : evalStaticExpr rhs with
      | none =>
        simpa [wp, h] using (SepLog.entails_refl ((Q CVal.undef) ∗ R))
      | some v =>
        simpa [wp, h] using (SepLog.entails_refl ((Q v) ∗ R))
    | deref p =>
      intro h ⟨h12, hR, hdis12R, hEq, hwp, hframe⟩
      rcases hwp with ⟨addr, vOld, vNew, h1, h2, hdis12, hEq12, hstore, hwand⟩
      have hdisUnion : Finmap.Disjoint (Heap.union h1 h2) hR := by
        simpa [Heap.union, hEq12] using hdis12R
      have hparts := (Finmap.disjoint_union_left h1 h2 hR).mp hdisUnion
      have hdisStore : Finmap.Disjoint h1 (Heap.union h2 hR) := by
        simpa [Heap.union] using
          (Finmap.disjoint_union_right h1 h2 hR).2 ⟨hdis12, hparts.1⟩
      have hwandFrame : (store addr vNew -∗ (Q CVal.undef ∗ R)) (Heap.union h2 hR) := by
        exact wand_frame _ _ _ _ ⟨h2, hR, hparts.2, rfl, hwand, hframe⟩
      refine ⟨addr, vOld, vNew, h1, Heap.union h2 hR, hdisStore, ?_, hstore, hwandFrame⟩
      calc
        h = Heap.union h12 hR := hEq
        _ = Heap.union (Heap.union h1 h2) hR := by rw [hEq12]
        _ = Heap.union h1 (Heap.union h2 hR) := by
              simp [Heap.union, Finmap.union_assoc]
    | fieldAccess p field =>
      intro h ⟨h12, hR, hdis12R, hEq, hwp, hframe⟩
      rcases hwp with ⟨addr, vOld, vNew, h1, h2, hdis12, hEq12, hstore, hwand⟩
      have hdisUnion : Finmap.Disjoint (Heap.union h1 h2) hR := by
        simpa [Heap.union, hEq12] using hdis12R
      have hparts := (Finmap.disjoint_union_left h1 h2 hR).mp hdisUnion
      have hdisStore : Finmap.Disjoint h1 (Heap.union h2 hR) := by
        simpa [Heap.union] using
          (Finmap.disjoint_union_right h1 h2 hR).2 ⟨hdis12, hparts.1⟩
      have hwandFrame : (store addr vNew -∗ (Q CVal.undef ∗ R)) (Heap.union h2 hR) := by
        exact wand_frame _ _ _ _ ⟨h2, hR, hparts.2, rfl, hwand, hframe⟩
      refine ⟨addr, vOld, vNew, h1, Heap.union h2 hR, hdisStore, ?_, hstore, hwandFrame⟩
      calc
        h = Heap.union h12 hR := hEq
        _ = Heap.union (Heap.union h1 h2) hR := by rw [hEq12]
        _ = Heap.union h1 (Heap.union h2 hR) := by
              simp [Heap.union, Finmap.union_assoc]
    | _ =>
      intro _
      simp [wp]
  | seq s1 s2 ih1 ih2 =>
    intro hs Q R
    rcases hs with ⟨hs1, hs2⟩
    exact SepLog.entails_trans _ (wp s1 (fun _ => wp s2 Q ∗ R)) _
      (ih1 hs1 _ _)
      (wp_mono s1 _ _ (fun _ => ih2 hs2 _ _))
  | ite cond thenBr elseBr ihThen ihElse =>
    intro hs Q R
    rcases hs with ⟨hsThen, hsElse⟩
    cases h : evalStaticExpr cond with
    | none =>
      intro hheap ⟨h1, h2, hdis, hEq, hcond, hR⟩
      have hcond' : HProp.hand (wp thenBr Q) (wp elseBr Q) h1 := by
        simpa [wp, h] using hcond
      rcases hcond' with ⟨hThen, hElse⟩
      have hThenFrame : (wp thenBr Q ∗ R) hheap := ⟨h1, h2, hdis, hEq, hThen, hR⟩
      have hElseFrame : (wp elseBr Q ∗ R) hheap := ⟨h1, h2, hdis, hEq, hElse, hR⟩
      simpa [wp, h] using
        (show HProp.hand (wp thenBr (fun v => Q v ∗ R)) (wp elseBr (fun v => Q v ∗ R)) hheap from
          ⟨ihThen hsThen _ _ _ hThenFrame, ihElse hsElse _ _ _ hElseFrame⟩)
    | some v =>
      by_cases hv : isTruthy v
      · simpa [wp, h, hv] using ihThen hsThen Q R
      · simpa [wp, h, hv] using ihElse hsElse Q R
  | whileInv cond inv body ih =>
    intro hs Q R
    cases hs
  | alloc x cells =>
    intro _ Q R h ⟨h1, h2, hdis, hEq, hwp, hR⟩
    rcases hwp with ⟨addr, hwand⟩
    exact ⟨addr, wand_frame _ _ _ _ ⟨h1, h2, hdis, hEq, hwand, hR⟩⟩
  | free e cells =>
    intro _ Q R
    cases e with
    | var x =>
      intro h ⟨h12, hR, hdis12R, hEq, hwp, hframe⟩
      rcases hwp with ⟨addr, vs, hlen, hblock⟩
      rcases hblock with ⟨h1, h2, hdis12, hEq12, hvals, hwand⟩
      have hdisUnion : Finmap.Disjoint (Heap.union h1 h2) hR := by
        simpa [Heap.union, hEq12] using hdis12R
      have hparts := (Finmap.disjoint_union_left h1 h2 hR).mp hdisUnion
      have hdisVals : Finmap.Disjoint h1 (Heap.union h2 hR) := by
        simpa [Heap.union] using
          (Finmap.disjoint_union_right h1 h2 hR).2 ⟨hdis12, hparts.1⟩
      have hwandFrame : (HProp.emp -∗ (Q CVal.undef ∗ R)) (Heap.union h2 hR) := by
        exact wand_frame _ _ _ _ ⟨h2, hR, hparts.2, rfl, hwand, hframe⟩
      refine ⟨addr, vs, hlen, ⟨h1, Heap.union h2 hR, hdisVals, ?_, hvals, hwandFrame⟩⟩
      calc
        h = Heap.union h12 hR := hEq
        _ = Heap.union (Heap.union h1 h2) hR := by rw [hEq12]
        _ = Heap.union h1 (Heap.union h2 hR) := by
              simp [Heap.union, Finmap.union_assoc]
    | _ =>
      intro _
      simp [wp]
  | decl x ty =>
    intro _ Q R
    exact SepLog.entails_refl _

/-- Monotonicity transported onto the Mem compatibility surface. -/
theorem wp_mono_onMem (s : CStmt) (Q Q' : CVal → HProp)
    (hpost : ∀ v, Q v ⊢ₛ Q' v) :
    wpOnMem s Q ⊢ₘ wpOnMem s Q' := by
  exact entails_onMem (wp_mono s Q Q' hpost)

/-- Frame rule transported onto the Mem compatibility surface by projecting
legacy heap assertions through block 0. This is phrased in terms of
`(P ∗ R).onMem`, not `P.onMem ∗ₘ R.onMem`, because the current theorem is a
compatibility result for the legacy heap logic rather than a proof that the
Mem-native separating conjunction coincides with the projected one. -/
theorem wp_frame_onMem (s : CStmt) (hs : FrameSafe s) (Q : CVal → HProp) (R : HProp) :
    (wp s Q ∗ R).onMem ⊢ₘ wpOnMem s (fun v => Q v ∗ R) := by
  exact entails_onMem (wp_frame s hs Q R)

end HeytingLean.LeanCP
