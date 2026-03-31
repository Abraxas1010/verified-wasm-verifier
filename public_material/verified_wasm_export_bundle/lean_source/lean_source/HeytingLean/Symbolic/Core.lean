namespace HeytingLean.Symbolic

inductive SymSort where
  | bool
  | int
  | real
  | bitvec (width : Nat)
  | array (domain : SymSort) (range : SymSort)
  deriving Repr, DecidableEq, Inhabited

structure SymbolDecl where
  name : String
  sort : SymSort
  deriving Repr, DecidableEq, Inhabited

inductive Expr where
  | var (decl : SymbolDecl)
  | boolLit (value : Bool)
  | intLit (value : Int)
  | realLit (repr : String)
  | app (fn : String) (args : List Expr) (sort : SymSort)
  deriving Repr

namespace Expr

def sort : Expr → SymSort
  | .var decl => decl.sort
  | .boolLit _ => .bool
  | .intLit _ => .int
  | .realLit _ => .real
  | .app _ _ s => s

private def insertDecl (decl : SymbolDecl) (acc : List SymbolDecl) : List SymbolDecl :=
  if acc.any (fun d => d.name = decl.name) then acc else decl :: acc

def collectDecls : Expr → List SymbolDecl
  | .var decl => [decl]
  | .boolLit _ => []
  | .intLit _ => []
  | .realLit _ => []
  | .app _ args _ =>
      args.foldl (fun acc e => (collectDecls e).foldl (fun acc' d => insertDecl d acc') acc) []

end Expr

inductive Relation where
  | eq
  | ne
  | le
  | lt
  | ge
  | gt
  deriving Repr, DecidableEq, Inhabited

structure Constraint where
  lhs : Expr
  rhs : Expr
  rel : Relation
  deriving Repr

namespace Constraint

def decls (c : Constraint) : List SymbolDecl :=
  let fromLhs := Expr.collectDecls c.lhs
  let fromRhs := Expr.collectDecls c.rhs
  fromRhs.foldl
    (fun acc d => if acc.any (fun d' => d'.name = d.name) then acc else d :: acc)
    fromLhs

end Constraint

structure Problem where
  logic : String := "ALL"
  declarations : List SymbolDecl := []
  constraints : List Constraint := []
  tags : List String := []
  deriving Repr, Inhabited

namespace Problem

private def mergeDecls (base extra : List SymbolDecl) : List SymbolDecl :=
  extra.foldl
    (fun acc d => if acc.any (fun d' => d'.name = d.name) then acc else d :: acc)
    base

def withInferredDecls (p : Problem) : Problem :=
  let inferred := p.constraints.foldl (fun acc c => mergeDecls acc c.decls) []
  { p with declarations := mergeDecls p.declarations inferred }

def addConstraint (p : Problem) (c : Constraint) : Problem :=
  { p with constraints := p.constraints.concat c }

end Problem

end HeytingLean.Symbolic
