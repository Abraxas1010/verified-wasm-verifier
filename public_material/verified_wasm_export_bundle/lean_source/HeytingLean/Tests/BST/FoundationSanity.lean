import HeytingLean.BST.Foundation

namespace HeytingLean.Tests.BST.Foundation

open HeytingLean.BST

def U : UniverseBound := ⟨3, by decide⟩
def bounded123 : BoundedFinset U ℕ := ⟨{0, 1, 2}, by decide⟩

example : BForall ({0, 1, 2} : Finset ℕ) (fun n => n < 3) := by
  decide

example : BForallOn bounded123 (fun n => n < 3) := by
  decide

example : BExistsOn bounded123 (fun n => n = 1) := by
  decide

example : (bexistsChooseOn (s := bounded123) (p := fun n => n = 1) (by decide)).1 = 1 := by
  exact (bexistsChooseOn (s := bounded123) (p := fun n => n = 1) (by decide)).2.2

example : (BoundedFinset.pair? U 1 2).isSome = true := by
  decide

example :
    (BoundedFinset.powerset? (BoundedFinset.singleton U 1)).isSome = true := by
  decide

end HeytingLean.Tests.BST.Foundation
