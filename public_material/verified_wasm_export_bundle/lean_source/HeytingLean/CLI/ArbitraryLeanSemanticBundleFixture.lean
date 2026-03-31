namespace HeytingLean.CLI.ArbitraryLeanSemanticBundleFixture

def zeroNat : Nat := 0

theorem zeroNat_eq : zeroNat = 0 := rfl

def twoNat : Nat := Nat.succ (Nat.succ 0)

theorem twoNat_eq : twoNat = 2 := rfl

def idBool (b : Bool) : Bool := b

theorem idBool_true : idBool true = true := rfl

theorem idBool_false : idBool false = false := rfl

def constSeven : Nat := (fun x => x) 7

theorem constSeven_eq : constSeven = 7 := rfl

end HeytingLean.CLI.ArbitraryLeanSemanticBundleFixture
