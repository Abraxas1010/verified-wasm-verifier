import HeytingLean.Symbolic.Core

namespace HeytingLean.Symbolic

namespace TPTP

private def sanitizeNameChar (c : Char) : Char :=
  if c.isAlphanum || c = '_' then c else '_'

private def sanitizeName (s : String) : String :=
  let normalized := String.mk (s.data.map sanitizeNameChar)
  match normalized.data with
  | [] => "f"
  | c :: _ =>
      if c.isAlpha || c = '_' then normalized else s!"f_{normalized}"

private def sanitizeFunctor (fn : String) : String :=
  match fn with
  | "+" => "add"
  | "-" => "sub"
  | "*" => "mul"
  | "/" => "div"
  | "^" => "pow"
  | "=" => "eq"
  | "!=" => "neq"
  | "<" => "lt"
  | "<=" => "le"
  | ">" => "gt"
  | ">=" => "ge"
  | _ => sanitizeName fn

private def termToTPTP : Expr → String
  | .var decl => sanitizeName decl.name
  | .boolLit true => "$true"
  | .boolLit false => "$false"
  | .intLit n => toString n
  | .realLit repr => repr
  | .app fn args _ => s!"{sanitizeFunctor fn}({", ".intercalate (args.map termToTPTP)})"

private def relToTPTP : Relation → String
  | .eq => "="
  | .ne => "!="
  | .le => "<="
  | .lt => "<"
  | .ge => ">="
  | .gt => ">"

private def constraintToFormula (c : Constraint) : String :=
  s!"({termToTPTP c.lhs} {relToTPTP c.rel} {termToTPTP c.rhs})"

def problemToFOFAxioms (namePrefix : String) (p : Problem) : List String :=
  let safePrefix := sanitizeName namePrefix
  let indexed := (List.range p.constraints.length).zip p.constraints
  let role := "ax" ++ "iom"
  indexed.map (fun (i, c) => s!"fof({safePrefix}_{i}, {role}, {constraintToFormula c}).")

end TPTP

end HeytingLean.Symbolic
