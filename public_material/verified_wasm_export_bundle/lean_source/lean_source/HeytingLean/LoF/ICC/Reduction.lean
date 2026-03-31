import HeytingLean.LoF.ICC.ConservativeEmbedding

namespace HeytingLean
namespace LoF
namespace ICC

open HeytingLean.LoF

inductive Step : Term → Term → Prop where
  /-- SOURCE: ICC gist `APP` with `Lam`. -/
  | beta (body arg : Term) :
      Step (.app (.lam body) arg) (Term.subst0 arg body)
  /-- SOURCE: ICC gist `APP` with `Val`, translated from HOAS to de Bruijn syntax. -/
  | app_bridge (body arg : Term) :
      Step (.app (.bridge body) arg)
           (.bridge (.app body (.ann (.var 0) (arg.shift 1))))
  /-- SOURCE: ICC gist `ANN` with `Lam`, translated from HOAS to de Bruijn syntax. -/
  | ann_lam (val body : Term) :
      Step (.ann val (.lam body))
           (.lam (.ann (.app (val.shift 1) (.var 0)) (Term.subst0 (.bridge (.var 0)) body)))
  /-- SOURCE: ICC gist `ANN` with `Val`. -/
  | ann_bridge (val body : Term) :
      Step (.ann val (.bridge body)) (Term.subst0 val body)
  /-- HYPOTHESIS: local interoperability shim for `embedLegacy .Y`. -/
  | legacy_y (arg : Term) :
      Step (.app legacyY arg) (.app arg (.app legacyY arg))
  | app_left {fn fn' arg : Term} :
      Step fn fn' →
      Step (.app fn arg) (.app fn' arg)
  | app_right {fn arg arg' : Term} :
      Step arg arg' →
      Step (.app fn arg) (.app fn arg')
  | ann_left {val val' typ : Term} :
      Step val val' →
      Step (.ann val typ) (.ann val' typ)
  | ann_right {val typ typ' : Term} :
      Step typ typ' →
      Step (.ann val typ) (.ann val typ')

inductive Steps : Term → Term → Prop where
  | refl (t : Term) : Steps t t
  | trans {t u v : Term} : Step t u → Steps u v → Steps t v

theorem Steps.ofEq {t u : Term} (h : t = u) : Steps t u := by
  subst h
  exact .refl _

theorem Steps.app_left {fn fn' arg : Term} (h : Steps fn fn') :
    Steps (.app fn arg) (.app fn' arg) := by
  induction h with
  | refl t =>
      exact .refl _
  | trans hs hrest ih =>
      exact .trans (.app_left hs) ih

theorem Steps.app_right {fn arg arg' : Term} (h : Steps arg arg') :
    Steps (.app fn arg) (.app fn arg') := by
  induction h with
  | refl t =>
      exact .refl _
  | trans hs hrest ih =>
      exact .trans (.app_right hs) ih

def step? : Term → Option Term
  | .app (.bridge (.ann (.var 0) (.var 0))) arg => some (.app arg (.app legacyY arg))
  | .app (.lam body) arg => some (Term.subst0 arg body)
  | .app (.bridge body) arg => some (.bridge (.app body (.ann (.var 0) (arg.shift 1))))
  | .ann val (.lam body) => some (.lam (.ann (.app (val.shift 1) (.var 0)) (Term.subst0 (.bridge (.var 0)) body)))
  | .ann val (.bridge body) => some (Term.subst0 val body)
  | .app fn arg =>
      match step? fn with
      | some fn' => some (.app fn' arg)
      | none => (.app fn ·) <$> step? arg
  | .ann val typ =>
      match step? val with
      | some val' => some (.ann val' typ)
      | none => (.ann val ·) <$> step? typ
  | _ => none

def reduceFuel : Nat → Term → Term
  | 0, t => t
  | fuel + 1, t =>
      match step? t with
      | some u => reduceFuel fuel u
      | none => t

def containsLegacyYShim : Term → Bool
  | .var _ => false
  | .lam body => containsLegacyYShim body
  | .app fn arg => containsLegacyYShim fn || containsLegacyYShim arg
  | .bridge body =>
      if (.bridge body) = legacyY then
        true
      else
        containsLegacyYShim body
  | .ann val typ => containsLegacyYShim val || containsLegacyYShim typ

def isYFree : Term → Bool
  | t => !containsLegacyYShim t

def checkYFree (fuel : Nat) (t : Term) : Bool :=
  isYFree t && (step? (reduceFuel fuel t)).isNone

@[simp] theorem subst0_k_body (x : LoF.Comb) :
    Term.subst0 (embedLegacy x) (.lam (.var 1)) = .lam (embedLegacy x) := by
  simp [Term.subst0, Term.substAt]

@[simp] theorem subst0_s_body1 (x : LoF.Comb) :
    Term.subst0 (embedLegacy x)
      (.lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0))))) =
      .lam (.lam (.app (.app (embedLegacy x) (.var 0)) (.app (.var 1) (.var 0)))) := by
  simp [Term.subst0, Term.substAt]

@[simp] theorem subst0_s_body2 (x y : LoF.Comb) :
    Term.subst0 (embedLegacy y)
      (.lam (.app (.app (embedLegacy x) (.var 0)) (.app (.var 1) (.var 0)))) =
      .lam (.app (.app (embedLegacy x) (.var 0)) (.app (embedLegacy y) (.var 0))) := by
  have hClosed :
      Term.substAt 1 (embedLegacy y) (embedLegacy x) = embedLegacy x := by
    simpa using
      (Term.substAt_closedAbove_ge
        (k := 0)
        (cutoff := 1)
        (repl := embedLegacy y)
        (t := embedLegacy x)
        (closed_embedLegacy x)
        (by omega))
  simp [Term.subst0, Term.substAt, hClosed]

@[simp] theorem subst0_s_body3 (x y z : LoF.Comb) :
    Term.subst0 (embedLegacy z)
      (.app (.app (embedLegacy x) (.var 0)) (.app (embedLegacy y) (.var 0))) =
      .app (.app (embedLegacy x) (embedLegacy z)) (.app (embedLegacy y) (embedLegacy z)) := by
  simp [Term.subst0, Term.substAt]

theorem k_rule_steps (x y : LoF.Comb) :
    Steps (.app (.app kTerm (embedLegacy x)) (embedLegacy y)) (embedLegacy x) := by
  let mid : Term := .app (.lam (embedLegacy x)) (embedLegacy y)
  refine .trans (u := mid) ?_ ?_
  · simpa [mid, kTerm] using
      (Step.app_left (Step.beta (body := .lam (.var 1)) (arg := embedLegacy x)))
  · refine .trans (u := embedLegacy x) ?_ (.refl _)
    simpa [mid] using (Step.beta (body := embedLegacy x) (arg := embedLegacy y))

theorem s_rule_steps (x y z : LoF.Comb) :
    Steps (.app (.app (.app sTerm (embedLegacy x)) (embedLegacy y)) (embedLegacy z))
      (.app (.app (embedLegacy x) (embedLegacy z)) (.app (embedLegacy y) (embedLegacy z))) := by
  let mid1 : Term :=
    .app
      (.app
        (.lam (.lam (.app (.app (embedLegacy x) (.var 0)) (.app (.var 1) (.var 0)))))
        (embedLegacy y))
      (embedLegacy z)
  let mid2 : Term :=
    .app
      (.lam (.app (.app (embedLegacy x) (.var 0)) (.app (embedLegacy y) (.var 0))))
      (embedLegacy z)
  let out : Term :=
    .app (.app (embedLegacy x) (embedLegacy z)) (.app (embedLegacy y) (embedLegacy z))
  refine .trans (u := mid1) ?_ ?_
  · simpa [mid1, sTerm] using
      (Step.app_left (Step.app_left (Step.beta
        (body := .lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))
        (arg := embedLegacy x))))
  · refine .trans (u := mid2) ?_ ?_
    · simpa [mid1, mid2] using
        (Step.app_left (Step.beta
          (body := .lam (.app (.app (embedLegacy x) (.var 0)) (.app (.var 1) (.var 0))))
          (arg := embedLegacy y)))
    · refine .trans (u := out) ?_ (.refl _)
      simpa [mid2, out] using
        (Step.beta
          (body := .app (.app (embedLegacy x) (.var 0)) (.app (embedLegacy y) (.var 0)))
          (arg := embedLegacy z))

theorem y_rule_steps (f : LoF.Comb) :
    Steps (.app legacyY (embedLegacy f)) (.app (embedLegacy f) (.app legacyY (embedLegacy f))) := by
  let out : Term := .app (embedLegacy f) (.app legacyY (embedLegacy f))
  exact .trans (u := out) (Step.legacy_y _) (.refl _)

theorem legacy_step_starts {t u : LoF.Comb} (h : LoF.Comb.Step t u) :
    ∃ v : Term, Step (embedLegacy t) v := by
  induction h with
  | K_rule x y =>
      refine ⟨.app (.lam (embedLegacy x)) (embedLegacy y), ?_⟩
      simpa [kTerm] using
        (Step.app_left (Step.beta (body := .lam (.var 1)) (arg := embedLegacy x)))
  | S_rule x y z =>
      refine ⟨
        .app
          (.app
            (.lam (.lam (.app (.app (embedLegacy x) (.var 0)) (.app (.var 1) (.var 0)))))
            (embedLegacy y))
          (embedLegacy z),
        ?_⟩
      simpa [sTerm] using
        (Step.app_left (Step.app_left (Step.beta
          (body := .lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))
          (arg := embedLegacy x))))
  | Y_rule f =>
      refine ⟨.app (embedLegacy f) (.app legacyY (embedLegacy f)), ?_⟩
      exact .legacy_y _
  | app_left hs ih =>
      rename_i f f' a
      rcases ih with ⟨v, hv⟩
      exact ⟨.app v (embedLegacy a), .app_left hv⟩
  | app_right hs ih =>
      rename_i f a a'
      rcases ih with ⟨v, hv⟩
      exact ⟨.app (embedLegacy f) v, .app_right hv⟩

theorem legacy_step_preserved {t u : LoF.Comb} (h : LoF.Comb.Step t u) :
    Steps (embedLegacy t) (embedLegacy u) := by
  induction h with
  | K_rule x y =>
      simpa [embedLegacy] using k_rule_steps x y
  | S_rule x y z =>
      simpa [embedLegacy] using s_rule_steps x y z
  | Y_rule f =>
      simpa [embedLegacy] using y_rule_steps f
  | app_left hs ih =>
      simpa [embedLegacy] using Steps.app_left ih
  | app_right hs ih =>
      simpa [embedLegacy] using Steps.app_right ih

theorem ann_bridge_free_erase_preserves_nf {c : LoF.Comb}
    (hNormal : ∀ u : Term, ¬ Step (embedLegacy c) u) :
    LoF.Comb.Normal c := by
  intro u hStep
  rcases legacy_step_starts hStep with ⟨v, hv⟩
  exact hNormal v hv

end ICC
end LoF
end HeytingLean
