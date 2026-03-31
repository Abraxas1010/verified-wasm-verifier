import Mathlib

set_option autoImplicit false

namespace HeytingLean.Physics.FreeWill

/--
Abstract causal frame used to state "spacelike/no-signalling" side conditions
without committing to a specific spacetime model.
-/
structure CausalFrame (Event : Type*) where
  before : Event → Event → Prop
  before_trans : Transitive before
  before_irrefl : Irreflexive before

/-- Two events are spacelike-separated when neither causally precedes the other. -/
def Spacelike {Event : Type*} (K : CausalFrame Event) (e₁ e₂ : Event) : Prop :=
  ¬ K.before e₁ e₂ ∧ ¬ K.before e₂ e₁

theorem spacelike_symm {Event : Type*} (K : CausalFrame Event) (e₁ e₂ : Event) :
    Spacelike K e₁ e₂ → Spacelike K e₂ e₁ := by
  intro h
  exact ⟨h.2, h.1⟩

/-- Information accessible at an event, abstracted as a set of facts. -/
structure AccessibleInfo (Event Fact : Type*) where
  facts : Event → Set Fact

/-- Two events are informationally equivalent when they have identical accessible facts. -/
def SameAccessibleInfo {Event Fact : Type*}
    (I : AccessibleInfo Event Fact) (e₁ e₂ : Event) : Prop :=
  I.facts e₁ = I.facts e₂

/-- Event packaging for A-wing responses in locality semantics. -/
abbrev AEvent (InfoA LocalA LocalB : Type*) := InfoA × LocalA × LocalB

/-- Event packaging for B-wing responses in locality semantics. -/
abbrev BEvent (InfoB LocalB LocalA : Type*) := InfoB × LocalB × LocalA

/--
Locality principle for A-wing:
equal accessible information implies equal A-response, even if remote
choice differs.
-/
def LocalityA
    {InfoA LocalA LocalB OutA FactA : Type*}
    (I : AccessibleInfo (AEvent InfoA LocalA LocalB) FactA)
    (respA : InfoA → LocalA → LocalB → OutA) : Prop :=
  ∀ i a b₁ b₂,
    SameAccessibleInfo I (i, a, b₁) (i, a, b₂) →
      respA i a b₁ = respA i a b₂

/--
Locality principle for B-wing:
equal accessible information implies equal B-response, even if remote
choice differs.
-/
def LocalityB
    {InfoB LocalB LocalA OutB FactB : Type*}
    (I : AccessibleInfo (BEvent InfoB LocalB LocalA) FactB)
    (respB : InfoB → LocalB → LocalA → OutB) : Prop :=
  ∀ i b a₁ a₂,
    SameAccessibleInfo I (i, b, a₁) (i, b, a₂) →
      respB i b a₁ = respB i b a₂

/--
Spacelike/no-signalling accessibility condition for A-wing:
remote choices are invisible in A's accessible info.
-/
def RemoteChoiceInvisibleA
    {InfoA LocalA LocalB FactA : Type*}
    (I : AccessibleInfo (AEvent InfoA LocalA LocalB) FactA) : Prop :=
  ∀ i a b₁ b₂, SameAccessibleInfo I (i, a, b₁) (i, a, b₂)

/--
Spacelike/no-signalling accessibility condition for B-wing:
remote choices are invisible in B's accessible info.
-/
def RemoteChoiceInvisibleB
    {InfoB LocalB LocalA FactB : Type*}
    (I : AccessibleInfo (BEvent InfoB LocalB LocalA) FactB) : Prop :=
  ∀ i b a₁ a₂, SameAccessibleInfo I (i, b, a₁) (i, b, a₂)

/--
Factoring condition for A-wing accessible information:
facts are determined by local data only (`InfoA` + `LocalA`), independent of
remote B-choice.
-/
def FactorsA
    {InfoA LocalA LocalB FactA : Type*}
    (I : AccessibleInfo (AEvent InfoA LocalA LocalB) FactA) : Prop :=
  ∃ localFacts : InfoA → LocalA → Set FactA,
    ∀ i a b, I.facts (i, a, b) = localFacts i a

/--
Factoring condition for B-wing accessible information:
facts are determined by local data only (`InfoB` + `LocalB`), independent of
remote A-choice.
-/
def FactorsB
    {InfoB LocalB LocalA FactB : Type*}
    (I : AccessibleInfo (BEvent InfoB LocalB LocalA) FactB) : Prop :=
  ∃ localFacts : InfoB → LocalB → Set FactB,
    ∀ i b a, I.facts (i, b, a) = localFacts i b

theorem factorsA_implies_remoteInvisibleA
    {InfoA LocalA LocalB FactA : Type*}
    (I : AccessibleInfo (AEvent InfoA LocalA LocalB) FactA)
    (hFactors : FactorsA I) :
    RemoteChoiceInvisibleA I := by
  intro i a b₁ b₂
  rcases hFactors with ⟨localFacts, hLocal⟩
  dsimp [SameAccessibleInfo]
  simp [hLocal]

theorem factorsB_implies_remoteInvisibleB
    {InfoB LocalB LocalA FactB : Type*}
    (I : AccessibleInfo (BEvent InfoB LocalB LocalA) FactB)
    (hFactors : FactorsB I) :
    RemoteChoiceInvisibleB I := by
  intro i b a₁ a₂
  rcases hFactors with ⟨localFacts, hLocal⟩
  dsimp [SameAccessibleInfo]
  simp [hLocal]

/--
`MIN`-style remote-choice independence:
- A-wing outcomes do not depend on remote B-setting.
- B-wing outcomes do not depend on remote A-setting.
-/
def MIN {InfoA InfoB LocalA LocalB OutA OutB : Type*}
    (respA : InfoA → LocalA → LocalB → OutA)
    (respB : InfoB → LocalB → LocalA → OutB) : Prop :=
  (∀ iA a b₁ b₂, respA iA a b₁ = respA iA a b₂) ∧
  (∀ iB b a₁ a₂, respB iB b a₁ = respB iB b a₂)

/--
Derive `MIN` from explicit locality + accessibility assumptions.
-/
theorem min_of_spacelike_locality
    {InfoA InfoB LocalA LocalB OutA OutB FactA FactB : Type*}
    (IA : AccessibleInfo (AEvent InfoA LocalA LocalB) FactA)
    (IB : AccessibleInfo (BEvent InfoB LocalB LocalA) FactB)
    (respA : InfoA → LocalA → LocalB → OutA)
    (respB : InfoB → LocalB → LocalA → OutB)
    (hLocA : LocalityA IA respA)
    (hLocB : LocalityB IB respB)
    (hNoSigA : RemoteChoiceInvisibleA IA)
    (hNoSigB : RemoteChoiceInvisibleB IB) :
    MIN respA respB := by
  constructor
  · intro iA a b₁ b₂
    exact hLocA iA a b₁ b₂ (hNoSigA iA a b₁ b₂)
  · intro iB b a₁ a₂
    exact hLocB iB b a₁ a₂ (hNoSigB iB b a₁ a₂)

/--
Physical variant: derive `MIN` from locality plus explicit information
factorization (local facts only), avoiding direct no-signalling assumptions.
-/
theorem min_of_locality_and_factoring
    {InfoA InfoB LocalA LocalB OutA OutB FactA FactB : Type*}
    (IA : AccessibleInfo (AEvent InfoA LocalA LocalB) FactA)
    (IB : AccessibleInfo (BEvent InfoB LocalB LocalA) FactB)
    (respA : InfoA → LocalA → LocalB → OutA)
    (respB : InfoB → LocalB → LocalA → OutB)
    (hLocA : LocalityA IA respA)
    (hLocB : LocalityB IB respB)
    (hFactA : FactorsA IA)
    (hFactB : FactorsB IB) :
    MIN respA respB := by
  exact min_of_spacelike_locality IA IB respA respB hLocA hLocB
    (factorsA_implies_remoteInvisibleA IA hFactA)
    (factorsB_implies_remoteInvisibleB IB hFactB)

theorem min_left {InfoA InfoB LocalA LocalB OutA OutB : Type*}
    {respA : InfoA → LocalA → LocalB → OutA}
    {respB : InfoB → LocalB → LocalA → OutB}
    (hMIN : MIN respA respB) :
    ∀ iA a b₁ b₂, respA iA a b₁ = respA iA a b₂ :=
  hMIN.1

theorem min_right {InfoA InfoB LocalA LocalB OutA OutB : Type*}
    {respA : InfoA → LocalA → LocalB → OutA}
    {respB : InfoB → LocalB → LocalA → OutB}
    (hMIN : MIN respA respB) :
    ∀ iB b a₁ a₂, respB iB b a₁ = respB iB b a₂ :=
  hMIN.2

end HeytingLean.Physics.FreeWill
