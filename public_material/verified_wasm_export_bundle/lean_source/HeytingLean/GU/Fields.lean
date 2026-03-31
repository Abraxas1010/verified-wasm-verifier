import HeytingLean.GU.Observerse

/-!
# GU.Fields (minimal, compile-first)

The DOCX blueprint distinguishes:
- fields native to `X` vs `Y`,
- “observer fields” (the embedding maps viewed as fields),
- “invasive fields” (pullbacks of `Y`-fields to `X`).

In this initial scaffold, we model a “field” as a plain function.
This keeps the layer usable immediately and lets later phases refine to bundles/sections.
-/

namespace HeytingLean
namespace GU

universe u v w

abbrev Field (X : Type u) (V : Type v) : Type (max u v) :=
  X → V

namespace Field

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pull back a `Y`-field along an observer embedding `ι : X → Y`. -/
def pullback (obs : Observerse X Y) {V : Type w} (φ : Field Y V) : Field X V :=
  fun x => φ (obs.toFun x)

/-- The observer map itself can be viewed as a `Y`-valued field on `X`. -/
def observerMap (obs : Observerse X Y) : Field X Y :=
  obs.toFun

/-! ## Native vs invasive fields -/

/-- A field on `X` is *invasive* (relative to `obs : X ↪ Y`) if it is a pullback of some
field on `Y`. -/
def IsInvasive (obs : Observerse X Y) {V : Type w} (φ : Field X V) : Prop :=
  ∃ ψ : Field Y V, φ = pullback obs ψ

/-- A field on `X` is *native* (relative to `obs : X ↪ Y`) if it is not invasive. -/
def IsNative (obs : Observerse X Y) {V : Type w} (φ : Field X V) : Prop :=
  ¬ IsInvasive (obs := obs) φ

theorem isInvasive_pullback (obs : Observerse X Y) {V : Type w} (ψ : Field Y V) :
    IsInvasive (obs := obs) (pullback obs ψ) :=
  ⟨ψ, rfl⟩

@[simp] theorem pullback_id {V : Type w} (φ : Field X V) :
    pullback (Observerse.id X) φ = φ := rfl

@[simp] theorem pullback_comp {Z : Type _} [TopologicalSpace Z]
    (obsXY : Observerse X Y) (obsYZ : Observerse Y Z) {V : Type w} (φ : Field Z V) :
    pullback (Observerse.comp obsXY obsYZ) φ = pullback obsXY (pullback obsYZ φ) := rfl

notation obs "^*" φ => pullback obs φ

end Field

end GU
end HeytingLean
