import Std
import HeytingLean.BountyHunter.Solc.YulTextMini.Types

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.Pretty

Deterministic pretty-printer for the YulTextMini AST.

This is used for Sprint 3 “bidirectional subset” validation:
`pretty` should be stable under `parseStmtsFromStringE` (Parse.lean).
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

private def escapeString (s : String) : String :=
  -- Minimal deterministic escaping (sufficient for our test corpora).
  s.foldl (fun acc c => if c = '"' then acc ++ "\\\"" else if c = '\\' then acc ++ "\\\\" else acc.push c) ""

partial def exprToString : Expr → String
  | .ident name => name
  | .nat n => toString n
  | .str s => s!"\"{escapeString s}\""
  | .bool true => "true"
  | .bool false => "false"
  | .call fn args =>
      let inner := String.intercalate "," (args.toList.map exprToString)
      s!"{fn}({inner})"

private def litToString : Lit → String
  | .nat n => toString n
  | .str s => s!"\"{escapeString s}\""
  | .bool true => "true"
  | .bool false => "false"

private def indentLines (n : Nat) (s : String) : String :=
  let pad := (List.replicate n ' ').asString
  String.intercalate "\n" (s.splitOn "\n" |>.map (fun line => if line = "" then line else pad ++ line))

mutual
  partial def stmtToString (s : Stmt) (indent : Nat := 0) : String :=
    match s with
    | .let_ name rhs => indentLines indent s!"let {name} := {exprToString rhs}"
    | .letMany names rhs =>
        let lhs := String.intercalate "," names.toList
        indentLines indent s!"let {lhs} := {exprToString rhs}"
    | .assign name rhs => indentLines indent s!"{name} := {exprToString rhs}"
    | .assignMany names rhs =>
        let lhs := String.intercalate "," names.toList
        indentLines indent s!"{lhs} := {exprToString rhs}"
    | .expr e => indentLines indent (exprToString e)
    | .block ss =>
        let inner := stmtsToString ss (indent + 2)
        indentLines indent ("{\n" ++ inner ++ "\n}")
    | .if_ cond thenStmts =>
        let inner := stmtsToString thenStmts (indent + 2)
        indentLines indent ("if " ++ exprToString cond ++ " {\n" ++ inner ++ "\n}")
    | .switch_ scrut cases def? =>
        let head := indentLines indent s!"switch {exprToString scrut}"
        let casesS :=
          cases.toList.map (fun (lit, body) =>
            let inner := stmtsToString body (indent + 2)
            indentLines indent ("case " ++ litToString lit ++ " {\n" ++ inner ++ "\n}"))
        let defS :=
          match def? with
          | none => []
          | some body =>
              let inner := stmtsToString body (indent + 2)
              [indentLines indent ("default {\n" ++ inner ++ "\n}")]
        String.intercalate "\n" ([head] ++ casesS ++ defS)
    | .for_ init cond post body =>
        let initS := stmtsToString init (indent + 2)
        let postS := stmtsToString post (indent + 2)
        let bodyS := stmtsToString body (indent + 2)
        indentLines indent ("for {\n" ++ initS ++ "\n} " ++ exprToString cond ++ " {\n" ++
          postS ++ "\n} {\n" ++ bodyS ++ "\n}")
    | .break => indentLines indent "break"
    | .continue => indentLines indent "continue"
    | .return_ args =>
        if args.isEmpty then
          indentLines indent "return"
        else
          let inner := String.intercalate "," (args.toList.map exprToString)
          indentLines indent ("return(" ++ inner ++ ")")
    | .revert args =>
        if args.isEmpty then
          indentLines indent "revert"
        else
          let inner := String.intercalate "," (args.toList.map exprToString)
          indentLines indent ("revert(" ++ inner ++ ")")
    | .leave => indentLines indent "leave"

  partial def stmtsToString (ss : Array Stmt) (indent : Nat := 0) : String :=
    String.intercalate "\n" (ss.toList.map (fun s => stmtToString s indent))
end

def stmtsToCanonicalString (ss : Array Stmt) : String :=
  stmtsToString ss 0

end HeytingLean.BountyHunter.Solc.YulTextMini
