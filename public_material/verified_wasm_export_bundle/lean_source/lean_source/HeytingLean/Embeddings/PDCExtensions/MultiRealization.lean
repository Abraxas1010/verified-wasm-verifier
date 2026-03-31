import HeytingLean.Embeddings.PerspectivalDescentHierarchy

/-!
# Embeddings.PDCExtensions.MultiRealization

Family G representatives:
- motivic realization perspectives
- prismatic-site perspectives
- Arakelov place perspectives
-/

namespace HeytingLean
namespace Embeddings
namespace PDCExtensions

/-! ## G1: Motivic realization -/

inductive MotivicPerspective where
  | betti | deRham | etale2 | etale3 | crystalline
  deriving DecidableEq, Repr, Inhabited

instance : Fintype MotivicPerspective where
  elems := {.betti, .deRham, .etale2, .etale3, .crystalline}
  complete t := by cases t <;> simp

instance motivicPDC :
    PDCWithDescent MotivicPerspective (fun _ => Int) where
  integral t :=
    match t with
    | .etale2 | .etale3 => {x | x % 2 = 0}
    | .betti | .deRham | .crystalline => {x | x = 0}
  finiteness x := by
    exact
      Set.toFinite
        {t : MotivicPerspective |
          x t ∉
            (match t with
             | .etale2 | .etale3 => ({y : Int | y % 2 = 0} : Set Int)
             | .betti | .deRham | .crystalline => ({y : Int | y = 0} : Set Int))}
  truncate _ k x := if k = 0 then 0 else x
  Plato := Int
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .betti
  amalgamate x hx := ⟨x .betti, by intro t; exact (hx t).symm⟩

theorem motivic_truncate_at_zero (t : MotivicPerspective) (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := MotivicPerspective) (Carrier := fun _ => Int) t 0 x = 0 := by
  simp [PerspectivalDescentCarrier.truncate]

/-! ## G2: Prismatic perspectives -/

inductive PrismaticPerspective where
  | prismA | prismB | prismC
  deriving DecidableEq, Repr, Inhabited

instance : Fintype PrismaticPerspective where
  elems := {.prismA, .prismB, .prismC}
  complete t := by cases t <;> simp

instance prismaticPDC :
    PDCWithDescent PrismaticPerspective (fun _ => Int) where
  integral _ := {x | x = 0}
  finiteness x := by
    exact Set.toFinite {t : PrismaticPerspective | x t ≠ 0}
  truncate _ k x := x % Int.ofNat (k + 1)
  Plato := Int
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .prismA
  amalgamate x hx := ⟨x .prismA, by intro t; exact (hx t).symm⟩

theorem prismatic_truncate_modulus (t : PrismaticPerspective) (k : Nat) (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := PrismaticPerspective) (Carrier := fun _ => Int) t k x =
        x % Int.ofNat (k + 1) := by
  rfl

/-! ## G3: Arakelov places -/

inductive ArakelovPlace where
  | p2 | p3 | p5 | archInf
  deriving DecidableEq, Repr, Inhabited

instance : Fintype ArakelovPlace where
  elems := {.p2, .p3, .p5, .archInf}
  complete t := by cases t <;> simp

def arakelovScale : ArakelovPlace → Nat
  | .p2 => 2
  | .p3 => 3
  | .p5 => 5
  | .archInf => 1

instance arakelovPDC :
    PDCWithDescent ArakelovPlace (fun _ => Int) where
  integral _ := {x | x = 0}
  finiteness x := by
    exact Set.toFinite {t : ArakelovPlace | x t ≠ 0}
  truncate t k x := x % Int.ofNat (arakelovScale t * (k + 1))
  Plato := Int
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .archInf
  amalgamate x hx := ⟨x .archInf, by intro t; exact (hx t).symm⟩

theorem arakelov_forward_cocycle :
    PDCWithTransport.ForwardCocycle
      (τ := ArakelovPlace) (Carrier := fun _ => Int) := by
  simpa using
    (PDCWithTransport.forward_is_cocycle
      (τ := ArakelovPlace) (Carrier := fun _ => Int))

end PDCExtensions
end Embeddings
end HeytingLean
