import HeytingLean.Symbolic.Core
import HeytingLean.Bridge.Solvers.SMTEmit

namespace HeytingLean.Symbolic

open HeytingLean.Bridge.Solvers

namespace SMT

private structure UFunSig where
  name : String
  argSorts : List SymSort
  resultSort : SymSort
  deriving Repr, DecidableEq

private def sortToSMT : SymSort → SMTSort
  | .bool => .bool
  | .int => .int
  | .real => .real
  | .bitvec w => .bitvec w
  | .array d r => .array (sortToSMT d) (sortToSMT r)

private def sortToSMTString : SymSort → String
  | .bool => "Bool"
  | .int => "Int"
  | .real => "Real"
  | .bitvec w => s!"(_ BitVec {w})"
  | .array d r => s!"(Array {sortToSMTString d} {sortToSMTString r})"

private def isNumericSort : SymSort → Bool
  | .int => true
  | .real => true
  | _ => false

private def isBitVecSort : SymSort → Bool
  | .bitvec _ => true
  | _ => false

private def allSameSort (args : List SymSort) : Bool :=
  match args with
  | [] => true
  | x :: xs => xs.all (fun y => y = x)

private def allBitVecSameWidth (args : List SymSort) : Bool :=
  match args with
  | [] => false
  | .bitvec w :: rest => rest.all (fun
      | .bitvec w' => w' = w
      | _ => false)
  | _ => false

private def isReservedBuiltInName (fn : String) : Bool :=
  fn = "=" || fn = "distinct" || fn = "not" || fn = "and" || fn = "or" || fn = "xor" ||
  fn = "=>" || fn = "ite" || fn = "+" || fn = "-" || fn = "*" || fn = "/" ||
  fn = "div" || fn = "mod" || fn = "abs" || fn = "<" || fn = "<=" || fn = ">" || fn = ">=" ||
  fn = "pow" || fn = "exp" || fn = "log" || fn = "sin" || fn = "cos" || fn = "tan" ||
  fn = "sqrt" || fn = "min" || fn = "max" || fn = "to_real" || fn = "to_int" ||
  fn = "bvnot" || fn = "bvneg" || fn = "bvand" || fn = "bvor" || fn = "bvxor" ||
  fn = "bvadd" || fn = "bvsub" || fn = "bvmul" || fn = "bvudiv" || fn = "bvurem" ||
  fn = "bvshl" || fn = "bvlshr" || fn = "bvult" || fn = "bvule" || fn = "bvugt" || fn = "bvuge" ||
  fn = "select" || fn = "store"

private def builtInMatchesSig (fn : String) (args : List SymSort) (result : SymSort) : Bool :=
  match fn with
  | "=" =>
      result = .bool && args.length ≥ 2 && allSameSort args
  | "distinct" =>
      result = .bool && args.length ≥ 2 && allSameSort args
  | "not" =>
      args = [.bool] && result = .bool
  | "and" | "or" | "xor" | "=>" =>
      result = .bool && args.length ≥ 2 && args.all (fun s => s = .bool)
  | "ite" =>
      match args with
      | cond :: tBranch :: fBranch :: [] =>
          cond = .bool && tBranch = fBranch && result = tBranch
      | _ => false
  | "+" | "*" =>
      args.length ≥ 2 &&
      allSameSort args &&
      args.all isNumericSort &&
      result = args.headD .int
  | "-" | "/" =>
      args.length ≥ 1 &&
      allSameSort args &&
      args.all isNumericSort &&
      result = args.headD .int
  | "div" | "mod" =>
      args.length = 2 && args = [.int, .int] && result = .int
  | "abs" =>
      args.length = 1 && args.headD .bool = .real && result = .real
  | "<" | "<=" | ">" | ">=" =>
      args.length = 2 && allSameSort args && args.all isNumericSort && result = .bool
  | "pow" =>
      args.length = 2 && args = [.real, .real] && result = .real
  | "exp" | "log" | "sin" | "cos" | "tan" | "sqrt" =>
      args = [.real] && result = .real
  | "min" | "max" =>
      args.length = 2 && allSameSort args && args.all isNumericSort && result = args.headD .int
  | "to_real" =>
      args = [.int] && result = .real
  | "to_int" =>
      args = [.real] && result = .int
  | "bvnot" | "bvneg" =>
      args.length = 1 && isBitVecSort (args.headD .bool) && result = args.headD .bool
  | "bvand" | "bvor" | "bvxor" | "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvshl" | "bvlshr" =>
      args.length = 2 && allBitVecSameWidth args && result = args.headD .bool
  | "bvult" | "bvule" | "bvugt" | "bvuge" =>
      args.length = 2 && allBitVecSameWidth args && result = .bool
  | "select" =>
      match args with
      | .array d r :: idx :: [] => idx = d && result = r
      | _ => false
  | "store" =>
      match args with
      | .array d r :: idx :: val :: [] => idx = d && val = r && result = .array d r
      | _ => false
  | _ => false

private def isBuiltInApp (fn : String) (args : List Expr) (result : SymSort) : Bool :=
  let argSorts := args.map Expr.sort
  builtInMatchesSig fn argSorts result || isReservedBuiltInName fn

private def insertSig (sig : UFunSig) (acc : List UFunSig) : List UFunSig :=
  if acc.any (fun s => s = sig) then acc else sig :: acc

private def collectUFunsExpr : Expr → List UFunSig
  | .var _ => []
  | .boolLit _ => []
  | .intLit _ => []
  | .realLit _ => []
  | .app fn args sort =>
      let childSigs :=
        args.foldl
          (fun acc arg => (collectUFunsExpr arg).foldl (fun acc' sig => insertSig sig acc') acc)
          []
      if isBuiltInApp fn args sort then
        childSigs
      else
        insertSig { name := fn, argSorts := args.map Expr.sort, resultSort := sort } childSigs

private def collectUFunsConstraint (c : Constraint) : List UFunSig :=
  let fromLhs := collectUFunsExpr c.lhs
  let fromRhs := collectUFunsExpr c.rhs
  fromRhs.foldl (fun acc sig => insertSig sig acc) fromLhs

private def exprToSMT : Expr → SMTTerm
  | .var decl => .const decl.name (sortToSMT decl.sort)
  | .boolLit true => .raw "true"
  | .boolLit false => .raw "false"
  | .intLit n => .lit n
  | .realLit repr => .raw repr
  | .app fn args _ => .app fn (args.map exprToSMT)

private def relFn : Relation → String
  | .eq => "="
  | .le => "<="
  | .lt => "<"
  | .ge => ">="
  | .gt => ">"
  | .ne => "="

private def constraintToSMT (c : Constraint) : SMTTerm :=
  match c.rel with
  | .ne => .app "not" [(.app "=" [exprToSMT c.lhs, exprToSMT c.rhs])]
  | _ => .app (relFn c.rel) [exprToSMT c.lhs, exprToSMT c.rhs]

private def declToSMTString (d : SymbolDecl) : String :=
  s!"(declare-const {d.name} {sortToSMTString d.sort})"

private def declFunToSMTString (sig : UFunSig) : String :=
  let args := String.intercalate " " (sig.argSorts.map sortToSMTString)
  s!"(declare-fun {sig.name} ({args}) {sortToSMTString sig.resultSort})"

def problemToSMTLIB2 (p : Problem) : String :=
  let p' := p.withInferredDecls
  let decls := p'.declarations.map declToSMTString
  let funDecls := p'.constraints.foldl (fun acc c =>
    (collectUFunsConstraint c).foldl (fun acc' sig => insertSig sig acc') acc) []
  let declFuns := funDecls.map declFunToSMTString
  let assertions := p'.constraints.map constraintToSMT
  wrapQuery p'.logic (decls ++ declFuns) assertions

end SMT

end HeytingLean.Symbolic
