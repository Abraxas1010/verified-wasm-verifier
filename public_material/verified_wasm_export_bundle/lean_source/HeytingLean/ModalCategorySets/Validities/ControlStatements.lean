import HeytingLean.ModalCategorySets.Validities.Pointed

namespace HeytingLean.ModalCategorySets.Validities

open HeytingLean.ModalCategorySets.Propositional

universe u v

namespace Formula

variable {α : Type v}

/-- The penultimate condition for a formula: false here, possible later, and once true
it becomes necessary. -/
def penultimate (φ : Formula α) : Formula α :=
  .conj (Formula.neg φ) (.conj (.dia φ) (.box (.imp φ (.box φ))))

/-- Grzegorczyk's axiom with an arbitrary formula substituted for the atom. -/
def grzOf (φ : Formula α) : Formula α :=
  .imp (.box (.imp (.box (.imp φ (.box φ))) φ)) φ

@[simp] theorem grzOf_var (p : α) :
    grzOf (.var p) = axiomGrz p :=
  rfl

end Formula

section ConeControl

variable {W : Type u} {α : Type v} (F : Frame W) (w : W) (val : W → α → Prop)

/-- A formula is necessary on the cone above `w` when it holds at every successor of `w`. -/
def NecessaryOnCone (φ : Formula α) : Prop :=
  ∀ u, F.rel w u → satisfies (mkModel F val) u φ

/-- A formula is possibly penultimate on the cone above `w` when some successor of `w`
satisfies the penultimate condition for it. -/
def PossiblyPenultimateOnCone (φ : Formula α) : Prop :=
  ∃ u, F.rel w u ∧ satisfies (mkModel F val) u (Formula.penultimate φ)

/-- Cone control for `φ`: either `φ` or `¬φ` is necessary on the cone, or one of them
becomes penultimate somewhere on the cone. -/
def ConeControlled (φ : Formula α) : Prop :=
  NecessaryOnCone F w val φ ∨
    NecessaryOnCone F w val (Formula.neg φ) ∨
      PossiblyPenultimateOnCone F w val φ ∨
        PossiblyPenultimateOnCone F w val (Formula.neg φ)

end ConeControl

theorem grzOf_true_of_coneControlled
    {W : Type u} {α : Type v} {F : Frame W} {w : W} {val : W → α → Prop}
    (hRefl : Reflexive F) (hTrans : Transitive F) {φ : Formula α}
    (hControl : ConeControlled F w val φ) :
    satisfies (mkModel F val) w (Formula.grzOf φ) := by
  intro hBox
  by_contra hNotPhi
  rcases hControl with hNecPhi | hRest
  · exact hNotPhi (hNecPhi w (hRefl w))
  · rcases hRest with hNecNotPhi | hRest
    · have hBoxStep : satisfies (mkModel F val) w (.box (.imp φ (.box φ))) := by
        intro u hwu hPhiU
        have hNotPhiU : satisfies (mkModel F val) u (Formula.neg φ) := hNecNotPhi u hwu
        exfalso
        exact hNotPhiU hPhiU
      exact hNotPhi (hBox w (hRefl w) hBoxStep)
    · rcases hRest with hPossPhi | hPossNotPhi
      · rcases hPossPhi with ⟨u, hwu, hPen⟩
        rcases hPen with ⟨hNotPhiU, hRest⟩
        rcases hRest with ⟨hDiaPhiU, hBoxStep⟩
        exact hNotPhiU (hBox u hwu hBoxStep)
      · rcases hPossNotPhi with ⟨u, hwu, hPen⟩
        rcases hPen with ⟨hPhiU, hRest⟩
        rcases hRest with ⟨hDiaNotPhiU, hBoxNotPhi⟩
        rcases hDiaNotPhiU with ⟨v, huv, hNotPhiV⟩
        have hBoxAtV : satisfies (mkModel F val) v (.box (.imp φ (.box φ))) := by
          intro z hvz hPhiZ
          have hNotPhiBoxV : satisfies (mkModel F val) v (.box (Formula.neg φ)) :=
            hBoxNotPhi v huv hNotPhiV
          have hNotPhiZ : satisfies (mkModel F val) z (Formula.neg φ) :=
            hNotPhiBoxV z hvz
          exfalso
          exact hNotPhiZ hPhiZ
        have hStepAtV : satisfies (mkModel F val) v (.imp (.box (.imp φ (.box φ))) φ) :=
          hBox v (hTrans w u v hwu huv)
        exact hNotPhiV (hStepAtV hBoxAtV)

theorem grzOf_validAt_of_coneControlled
    {W : Type u} {α : Type v} {F : Frame W} {w : W} (hRefl : Reflexive F) (hTrans : Transitive F)
    {φ : Formula α}
    (hControl : ∀ val, ConeControlled F w val φ) :
    F.ValidAt w (Formula.grzOf φ) := by
  intro val
  exact grzOf_true_of_coneControlled hRefl hTrans (hControl val)

theorem axiomGrz_validAt_of_coneControlled
    {W : Type u} {α : Type v} {F : Frame W} {w : W} (hRefl : Reflexive F) (hTrans : Transitive F)
    (p : α)
    (hControl : ∀ val, ConeControlled F w val (.var p)) :
    F.ValidAt w (axiomGrz p) := by
  simpa [Formula.grzOf_var] using
    (grzOf_validAt_of_coneControlled (F := F) (w := w) (φ := .var p) hRefl hTrans hControl)

theorem coneControlled_of_isolatedAt
    {W : Type u} {α : Type v} {F : Frame W} {w : W}
    (hIso : IsolatedAt F w) (val : W → α → Prop) (φ : Formula α) :
    ConeControlled F w val φ := by
  classical
  by_cases hPhi : satisfies (mkModel F val) w φ
  · left
    intro u hwu
    have hu : u = w := (hIso u).1 hwu
    simpa [hu] using hPhi
  · right
    left
    intro u hwu hPhiU
    have hu : u = w := (hIso u).1 hwu
    exact hPhi (by simpa [hu] using hPhiU)

theorem grzOf_validAt_of_isolatedAt
    {W : Type u} {α : Type v} {F : Frame W} {w : W}
    (hRefl : Reflexive F) (hTrans : Transitive F) (hIso : IsolatedAt F w) {φ : Formula α} :
    F.ValidAt w (Formula.grzOf φ) := by
  exact grzOf_validAt_of_coneControlled hRefl hTrans
    (fun val => coneControlled_of_isolatedAt hIso val φ)

end HeytingLean.ModalCategorySets.Validities
