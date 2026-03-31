namespace HeytingLean
namespace Policy

def budgetOk (pathAmounts : List Nat) (limit : Nat) : Bool :=
  let total := pathAmounts.foldl (· + ·) 0
  Nat.ble total limit

end Policy
end HeytingLean
