import HeytingLean.PTS.BaseExtension.Contextual.Encoding
import HeytingLean.PTS.BaseExtension.Contextual.Derives

namespace HeytingLean.PTS.BaseExtension.Contextual

/--
`SupportsCtx Γ B φ` is the redesigned contextual support judgment for the
goal-valued kernel. Unlike the legacy first-order bridge, the contextual kernel
stores encoded assumptions as first-class goals, so support is operational by
construction on this surface.
-/
def SupportsCtx (Γ : List IPL) (B : Base) (φ : IPL) : Prop :=
  SearchSupports (encodeBase B ++ encodeCtx Γ) (encode φ)

/--
`GoalSupportsCtx Δ B g` is the clause-level operational support judgment over
arbitrary goal contexts `Δ`.

This is the direct goal-language extension of `SupportsCtx`: instead of an IPL
context that must first be encoded, it works over first-class kernel goals.
-/
def GoalSupportsCtx (Δ : Program) (B : Base) (g : Goal) : Prop :=
  SearchSupports (encodeBase B ++ Δ) g

/--
`HeadGoalSupportsCtx Δ B g` is the clause-level operational support judgment
for goal contexts prefixed in front of the base.

This is the exact shape used by the residual conjunction callback surfaces,
which work in head contexts like `K :: encodeBase B`.
-/
def HeadGoalSupportsCtx (Δ : Program) (B : Base) (g : Goal) : Prop :=
  SearchSupports (Δ ++ encodeBase B) g

/--
Operational goal support for an arbitrary kernel goal from a base `B`.
-/
def GoalSupports (B : Base) (g : Goal) : Prop :=
  GoalSupportsCtx [] B g

/--
Head-context operational goal support for an arbitrary kernel goal from a base
`B`. At empty context this agrees with `GoalSupports`.
-/
def HeadGoalSupports (B : Base) (g : Goal) : Prop :=
  HeadGoalSupportsCtx [] B g

/--
`GoalFiresCtx Δ B g target` is the clause-level firing judgment for arbitrary
goals under an appended context `Δ`.

This is the direct firing analogue of `GoalSupportsCtx`: it records not only
that `g` is operationally meaningful in the kernel, but that it actually fires
to the requested target goal.
-/
def GoalFiresCtx (Δ : Program) (B : Base) (g : Goal) (target : AtomVar) : Prop :=
  Fires (encodeBase B ++ Δ) g target

/--
`HeadGoalFiresCtx Δ B g target` is the clause-level firing judgment for goal
contexts prefixed in front of the base.

This is the shape used by the surviving conjunction-backward recursive tail
callbacks, which operate in head contexts like `K :: encodeBase B`.
-/
def HeadGoalFiresCtx (Δ : Program) (B : Base) (g : Goal) (target : AtomVar) : Prop :=
  Fires (Δ ++ encodeBase B) g target

/--
Operational firing of an arbitrary kernel goal from a base `B`.
-/
def GoalFires (B : Base) (g : Goal) (target : AtomVar) : Prop :=
  GoalFiresCtx [] B g target

/--
Head-context operational firing of an arbitrary kernel goal from a base `B`.
At empty context this agrees with `GoalFires`.
-/
def HeadGoalFires (B : Base) (g : Goal) (target : AtomVar) : Prop :=
  HeadGoalFiresCtx [] B g target

/--
Operational support surface for the goal-valued contextual kernel.

This is intentionally named separately from `SemanticSupport.Supports` to avoid
colliding with the independent Sandqvist-style semantics used by the main
bridge theorem.
-/
def OperationalSupports (B : Base) (φ : IPL) : Prop :=
  SupportsCtx [] B φ

theorem supportsCtx_iff_searchCtx (Γ : List IPL) (B : Base) (φ : IPL) :
    SupportsCtx Γ B φ ↔ SearchSupports (encodeBase B ++ encodeCtx Γ) (encode φ) := by
  rfl

theorem goalSupportsCtx_iff_searchCtx (Δ : Program) (B : Base) (g : Goal) :
    GoalSupportsCtx Δ B g ↔ SearchSupports (encodeBase B ++ Δ) g := by
  rfl

theorem headGoalSupportsCtx_iff_searchCtx (Δ : Program) (B : Base) (g : Goal) :
    HeadGoalSupportsCtx Δ B g ↔ SearchSupports (Δ ++ encodeBase B) g := by
  rfl

theorem goalFiresCtx_iff_firesCtx (Δ : Program) (B : Base) (g : Goal) (target : AtomVar) :
    GoalFiresCtx Δ B g target ↔ Fires (encodeBase B ++ Δ) g target := by
  rfl

theorem headGoalFiresCtx_iff_firesCtx (Δ : Program) (B : Base) (g : Goal) (target : AtomVar) :
    HeadGoalFiresCtx Δ B g target ↔ Fires (Δ ++ encodeBase B) g target := by
  rfl

theorem operationalSupports_iff_search (B : Base) (φ : IPL) :
    OperationalSupports B φ ↔ SearchSupports (encodeBase B) (encode φ) := by
  simp [OperationalSupports, SupportsCtx, encodeCtx]

theorem goalSupports_iff_search (B : Base) (g : Goal) :
    GoalSupports B g ↔ SearchSupports (encodeBase B) g := by
  simp [GoalSupports, GoalSupportsCtx]

theorem headGoalSupports_iff_search (B : Base) (g : Goal) :
    HeadGoalSupports B g ↔ SearchSupports (encodeBase B) g := by
  simp [HeadGoalSupports, HeadGoalSupportsCtx]

theorem goalFires_iff_fires (B : Base) (g : Goal) (target : AtomVar) :
    GoalFires B g target ↔ Fires (encodeBase B) g target := by
  simp [GoalFires, GoalFiresCtx]

theorem headGoalFires_iff_fires (B : Base) (g : Goal) (target : AtomVar) :
    HeadGoalFires B g target ↔ Fires (encodeBase B) g target := by
  simp [HeadGoalFires, HeadGoalFiresCtx]

theorem goalSupportsCtx_encodeCtx_iff_supportsCtx
    (Γ : List IPL) (B : Base) (φ : IPL) :
    GoalSupportsCtx (encodeCtx Γ) B (encode φ) ↔ SupportsCtx Γ B φ := by
  rfl

theorem goalSupports_encode_iff_operationalSupports (B : Base) (φ : IPL) :
    GoalSupports B (encode φ) ↔ OperationalSupports B φ := by
  simp [GoalSupports, GoalSupportsCtx, OperationalSupports, SupportsCtx, encodeCtx]

theorem headGoalSupports_iff_goalSupports (B : Base) (g : Goal) :
    HeadGoalSupports B g ↔ GoalSupports B g := by
  simp [HeadGoalSupports, HeadGoalSupportsCtx, GoalSupports, GoalSupportsCtx]

theorem headGoalFires_iff_goalFires (B : Base) (g : Goal) (target : AtomVar) :
    HeadGoalFires B g target ↔ GoalFires B g target := by
  simp [HeadGoalFires, HeadGoalFiresCtx, GoalFires, GoalFiresCtx]

end Contextual
end HeytingLean.PTS.BaseExtension
