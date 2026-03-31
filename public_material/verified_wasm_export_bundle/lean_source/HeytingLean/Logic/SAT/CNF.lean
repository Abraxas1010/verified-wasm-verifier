/-!
# Minimal CNF + evaluation (bounded, tiny)

Tiny CNF representation for demo purposes. Variables are indexed by `Fin n`.
-/

namespace HeytingLean
namespace Logic
namespace SAT

structure Lit (n : Nat) where
  var : Fin n
  neg : Bool := false
deriving Repr, DecidableEq

abbrev Clause (n : Nat) := Array (Lit n)
abbrev CNF (n : Nat) := Array (Clause n)

def evalLit {n} (a : Fin n → Bool) (l : Lit n) : Bool :=
  let v := a l.var
  if l.neg then (!v) else v

def evalClause {n} (a : Fin n → Bool) (c : Clause n) : Bool :=
  c.any (fun l => evalLit a l)

def evalCNF {n} (a : Fin n → Bool) (f : CNF n) : Bool :=
  f.all (fun c => evalClause a c)

end SAT
end Logic
end HeytingLean

