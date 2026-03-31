import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 2: Nucleus as Lawvere-Tierney Topology
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

/-- Presheaf model used in this scaffold: data per agent. -/
abbrev Presheaf := Agent → Nat

/-- Plus construction (single pass). -/
def plus (P : Presheaf) : Presheaf :=
  fun A => closure (P A)

/-- Sheafification as `P⁺⁺`. -/
def sheafify (P : Presheaf) : Presheaf :=
  plus (plus P)

/-- Nucleus-style closure action on local sections. -/
def Rclosure (P : Presheaf) : Presheaf :=
  fun A => closure (P A)

/-- Inclusion functor from sheaves back to presheaves in this model. -/
def includeSheaf (P : Presheaf) : Presheaf := P

/-- `P⁺⁺` agrees with the declared sheafification operator. -/
theorem plus_construction (P : Presheaf) :
    ∀ A : Agent, plus (plus P) A = sheafify P A := by
  intro A
  rfl

/-- Catalog bridge: sheafification coincides with pointwise `R`-closure. -/
theorem sheafification_is_R (P : Presheaf) :
    ∀ A : Agent, sheafify P A = Rclosure P A := by
  intro A
  simp [sheafify, plus, Rclosure]

/-- Left-adjoint-style law in pointwise order, under sheaf-closed codomain sections. -/
theorem sheafification_left_adjoint (P Q : Presheaf)
    (hQClosed : ∀ A, closure (Q A) = Q A) :
    (∀ A, sheafify P A ≤ Q A) ↔ (∀ A, P A ≤ includeSheaf Q A) := by
  constructor
  · intro h A
    have h1 : P A ≤ closure (P A) := closure_extensive (P A)
    have h2 : closure (P A) ≤ sheafify P A := by
      unfold sheafify plus
      exact closure_extensive (closure (P A))
    have hQ : sheafify P A ≤ includeSheaf Q A := by
      simpa [includeSheaf] using h A
    exact Nat.le_trans h1 (Nat.le_trans h2 hQ)
  · intro h A
    have hLift : closure (P A) ≤ closure (Q A) := closure_monotone (h A)
    have hLift2 : closure (closure (P A)) ≤ closure (closure (Q A)) := closure_monotone hLift
    calc
      sheafify P A = closure (closure (P A)) := by rfl
      _ ≤ closure (closure (Q A)) := hLift2
      _ = closure (Q A) := closure_idempotent (Q A)
      _ = Q A := hQClosed A

end NucleusPOD
end HeytingLean
