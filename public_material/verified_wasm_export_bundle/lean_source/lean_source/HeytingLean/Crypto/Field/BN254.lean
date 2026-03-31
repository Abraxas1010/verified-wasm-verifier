namespace HeytingLean
namespace Crypto
namespace Field

def p : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

def norm (x : Nat) : Nat := x % p

def add (x y : Nat) : Nat := norm (x + y)
def mul (x y : Nat) : Nat := norm (x * y)

def pow (x : Nat) (k : Nat) : Nat :=
  let rec go (a : Nat) (e : Nat) (acc : Nat) : Nat :=
    if e = 0 then acc else
      let acc' := if e % 2 = 1 then mul acc a else acc
      go (mul a a) (e / 2) acc'
  go (norm x) k 1

end Field
end Crypto
end HeytingLean

