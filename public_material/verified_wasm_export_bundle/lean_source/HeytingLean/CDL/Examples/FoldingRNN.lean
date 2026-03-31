import HeytingLean.CDL.LaxAlgebraComonoid

/-!
# CDL example: a tiny “folding RNN” weight-tying lemma (2-step unroll)

CDL’s unrolling examples (Appendix J) emphasize that repeated reuse of a parametric cell
does **not** duplicate parameters: weight tying is enforced by reparameterization along
`Δ_P : P → P × P`.

To keep this repo’s scope Lean-realistic, we mechanize a minimal instance:

- a single parametric “cell” `cell : (A × S) ⟶ S` in `Para(Type)`,
- a 2-step unroll with *separate* parameters `(p₁, p₂) : P × P`,
- a tied 2-step unroll with a single parameter `p : P`,
- the explicit reparameterization `Δ p = (p, p)` witnessing equivalence.
-/

namespace HeytingLean
namespace CDL
namespace Examples

open HeytingLean.CDL.Para

universe u

variable {A S : Type u}

abbrev Cell (A S : Type u) : Type (u + 1) :=
  ParaHom (A × S) S

namespace FoldingRNN

variable (cell : Cell A S)

/-- Two-step unroll with separate parameters `(p₁, p₂) : P × P`. -/
def unroll2_sep : ParaHom (A × (A × S)) S :=
  ⟨cell.P × cell.P,
    fun
      | ((p₁, p₂), (a₁, (a₂, s))) =>
          cell.f (p₂, (a₂, cell.f (p₁, (a₁, s))))⟩

/-- Two-step unroll with a single parameter `p : P` used at both steps. -/
def unroll2_tied : ParaHom (A × (A × S)) S :=
  ⟨cell.P,
    fun
      | (p, (a₁, (a₂, s))) =>
          cell.f (p, (a₂, cell.f (p, (a₁, s))))⟩

/-- The diagonal tying map `Δ : P → P × P`. -/
def Δ : cell.P → (unroll2_sep (cell := cell)).P :=
  fun p => (p, p)

def unroll2_ties : Para2Hom (unroll2_sep (cell := cell)) (unroll2_tied (cell := cell)) :=
  ⟨Δ (cell := cell), by intro p x; rfl⟩

end FoldingRNN

end Examples
end CDL
end HeytingLean
