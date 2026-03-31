namespace HeytingLean
namespace Numbers

/-- von Neumann hierarchy skeleton. -/
inductive V : Nat → Type
| zero : V 0
| insert {n} (xs : List (Sigma V)) : V (n+1)

def V.shape : {n // True} → Type := fun ⟨n,_⟩ => V n

/-- Recover the rank from a dependent pair carrying an element of V. -/
def rankOf (x : Sigma V) : Nat := x.fst

end Numbers
end HeytingLean
