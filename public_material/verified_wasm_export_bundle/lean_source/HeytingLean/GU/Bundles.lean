import Mathlib.Topology.Sets.Opens
import Mathlib.GroupTheory.GroupAction.Basic
import HeytingLean.GU.Observerse

/-!
# GU.Bundles (minimal, compile-first)

GU is bundle-heavy (normal bundles, gauge bundles, spin bundles).
Mathlib has a substantial `FiberBundle`/`VectorBundle` framework, but GU’s intended “physics layer”
is not yet plug-and-play in our codebase.

This file provides a small *abstract* bundle interface (as data), sufficient to express:
- “a bundle over `X`”,
- “a section”,
- pullback bundles along an observer embedding.

Later phases can replace this with mathlib-native bundles once the target API is selected.
-/

namespace HeytingLean
namespace GU

universe u v w

structure Bundle (X : Type u) where
  fiber : X → Type*

abbrev Section {X : Type u} (E : Bundle (X := X)) : Type _ :=
  ∀ x : X, E.fiber x

abbrev TotalSpace {X : Type u} (E : Bundle (X := X)) : Type _ :=
  Sigma E.fiber

abbrev TotalSpace.proj {X : Type u} {E : Bundle (X := X)} : TotalSpace E → X :=
  Sigma.fst

structure BundleMap {X : Type u} (E F : Bundle (X := X)) where
  map : ∀ x : X, E.fiber x → F.fiber x

namespace Bundle

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pull back a bundle over `Y` along `ι : X → Y`. -/
def pullback (obs : Observerse X Y) (E : Bundle (X := Y)) : Bundle (X := X) :=
  { fiber := fun x => E.fiber (obs.toFun x) }

/-- Pull back a section along an observer embedding. -/
def pullbackSection (obs : Observerse X Y) (E : Bundle (X := Y)) (s : Section E) :
    Section (pullback obs E) :=
  fun x => s (obs.toFun x)

end Bundle

/-! ## Principal bundles (abstract but functional) -/

structure PrincipalBundle (X : Type u) (G : Type v) [Group G] where
  Total : Type w
  proj : Total → X
  right : Total → G → Total
  right_one : ∀ p : Total, right p 1 = p
  right_mul : ∀ p : Total, ∀ g h : G, right (right p g) h = right p (g * h)
  proj_right : ∀ p : Total, ∀ g : G, proj (right p g) = proj p

namespace PrincipalBundle

variable {X : Type u} {G : Type v} [Group G] (P : PrincipalBundle (X := X) (G := G))

abbrev Fiber (x : X) : Type _ :=
  { p : P.Total // P.proj p = x }

/-- The underlying bundle of points in the fiber over `x`. -/
def toBundle : Bundle (X := X) :=
  { fiber := fun x => P.Fiber x }

section Pullback

variable {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (obs : Observerse X Y)
variable (Q : PrincipalBundle (X := Y) (G := G))

/-- Pull back a principal bundle along an observer embedding. -/
def pullback : PrincipalBundle (X := X) (G := G) where
  Total := { q : X × Q.Total // Q.proj q.2 = obs.toFun q.1 }
  proj := fun q => q.1.1
  right := fun q g =>
    ⟨(q.1.1, Q.right q.1.2 g), by simpa [Q.proj_right] using q.2⟩
  right_one := by
    intro q
    ext <;> simp [Q.right_one]
  right_mul := by
    intro q g h
    ext <;> simp [Q.right_mul]
  proj_right := by
    intro q g
    rfl

end Pullback

section Associated

variable {V : Type _} [MulAction G V]

/-- The setoid defining the associated bundle quotient `P ×^G V`. -/
def associatedSetoid (P : PrincipalBundle (X := X) (G := G)) (V : Type _) [MulAction G V] :
    Setoid (P.Total × V) where
  r a b := ∃ g : G, b.1 = P.right a.1 g ∧ b.2 = g⁻¹ • a.2
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro a
      refine ⟨1, ?_, ?_⟩
      · simpa using (P.right_one a.1).symm
      · simp
    · rintro a b ⟨g, hb, hv⟩
      refine ⟨g⁻¹, ?_, ?_⟩
      · -- `a.1 = right b.1 g⁻¹`.
        calc
          a.1 = P.right a.1 1 := (P.right_one a.1).symm
          _ = P.right a.1 (g * g⁻¹) := by simp
          _ = P.right (P.right a.1 g) g⁻¹ := (P.right_mul a.1 g g⁻¹).symm
          _ = P.right b.1 g⁻¹ := by simp [hb]
      · -- `a.2 = (g⁻¹)⁻¹ • b.2`.
        calc
          a.2 = (1 : G) • a.2 := by simp
          _ = (g * g⁻¹) • a.2 := by simp
          _ = g • (g⁻¹ • a.2) := by simp [smul_smul]
          _ = g • b.2 := by simp [hv]
          _ = (g⁻¹)⁻¹ • b.2 := by simp
    · rintro a b c ⟨g₁, hb, hvb⟩ ⟨g₂, hc, hvc⟩
      refine ⟨g₁ * g₂, ?_, ?_⟩
      · -- `c.1 = right a.1 (g₁*g₂)`.
        calc
          c.1 = P.right b.1 g₂ := hc
          _ = P.right (P.right a.1 g₁) g₂ := by simp [hb]
          _ = P.right a.1 (g₁ * g₂) := P.right_mul a.1 g₁ g₂
      · -- `c.2 = (g₁*g₂)⁻¹ • a.2`.
        calc
          c.2 = g₂⁻¹ • b.2 := hvc
          _ = g₂⁻¹ • (g₁⁻¹ • a.2) := by simp [hvb]
          _ = (g₂⁻¹ * g₁⁻¹) • a.2 := by simp [smul_smul]
          _ = (g₁ * g₂)⁻¹ • a.2 := by simp

/-- Total space of the associated bundle `P ×^G V` as a quotient. -/
abbrev AssociatedTotal (P : PrincipalBundle (X := X) (G := G)) (V : Type _) [MulAction G V] :
    Type _ :=
  Quot (associatedSetoid (P := P) (V := V))

/-- Projection `P ×^G V → X`. -/
def associatedProj (P : PrincipalBundle (X := X) (G := G)) (V : Type _) [MulAction G V] :
    AssociatedTotal (P := P) (V := V) → X :=
  Quot.lift (fun pv : P.Total × V => P.proj pv.1) (by
    rintro a b ⟨g, hb, _⟩
    -- `proj` is invariant under the right action.
    have : P.proj a.1 = P.proj (P.right a.1 g) := (P.proj_right a.1 g).symm
    simpa [hb] using this )

/-- The associated bundle `P ×^G V` (as a GU `Bundle`). -/
def associatedBundle (P : PrincipalBundle (X := X) (G := G)) (V : Type _) [MulAction G V] :
    Bundle (X := X) :=
  { fiber := fun x => { q : AssociatedTotal (P := P) (V := V) // associatedProj (P := P) (V := V) q = x } }

end Associated

end PrincipalBundle

end GU
end HeytingLean
