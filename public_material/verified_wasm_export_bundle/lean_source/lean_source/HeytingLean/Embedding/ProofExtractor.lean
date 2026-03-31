import Lean
import Lean.Meta
import Lean.Data.Json
import Lean.Compiler.ExportAttr
import HeytingLean.Embedding.ASTExtractor
import HeytingLean.Embedding.Ast
import HeytingLean.Embedding.LambdaCoreExtractor
import HeytingLean.Util.ModuleOwner

namespace HeytingLean.Embedding

open Lean

private def truncateString (s : String) (maxChars : Nat) : String :=
  if s.length ≤ maxChars then
    s
  else
    (s.take maxChars) ++ "…<truncated>"

structure ExtractOptions where
  modulePrefixes : Array String := #[]
  namePrefixes : Array String := #[]
  /-- If provided, only include decls whose defining module is exactly this module. -/
  onlyModule : Option Name := none
  maxTheorems : Option Nat := none
  maxNodes : Nat := 20000
  maxConstsPerDecl : Nat := 2000
  includeDefs : Bool := false
  deriving Inhabited

private def moduleFor (env : Environment) (n : Name) : Name :=
  HeytingLean.Util.moduleOwnerOf env n

private def matchesAnyPrefix (s : String) (prefixes : Array String) : Bool :=
  prefixes.isEmpty || prefixes.any (fun p => s.startsWith p)

private def keepConst (env : Environment) (n : Name) (opts : ExtractOptions) : Bool :=
  let nameStr := n.toString
  if !matchesAnyPrefix nameStr opts.namePrefixes then
    false
  else
    let modStr := (moduleFor env n).toString
    let exactOk :=
      match opts.onlyModule with
      | none => true
      | some m => modStr == m.toString
    exactOk && matchesAnyPrefix modStr opts.modulePrefixes

private def proofInfoToJson
    (name : Name)
    (mod : Name)
    (kind : String)
    (declClass : String)
    (cSymbolGuess : String)
    (typeAst : AstTree)
    (valueAst : AstTree)
    (typeTruncated : Bool)
    (valueTruncated : Bool)
    (lambdaCoreTypeAst : AstTree)
    (lambdaCoreValueAst : AstTree)
    (lambdaCoreTypeTruncated : Bool)
    (lambdaCoreValueTruncated : Bool)
    (constsType : Array String)
    (constsValue : Array String)
    (constsTypeTruncated : Bool)
    (constsValueTruncated : Bool)
    (typePretty : Option String)
    (valuePretty : Option String)
    (doc : Option String) : Json :=
  let fields : Array (String × Json) := #[
    ("name", Json.str name.toString),
    ("module", Json.str mod.toString),
    ("decl_kind", Json.str kind),
    ("decl_class", Json.str declClass),
    ("c_symbol_guess", Json.str cSymbolGuess),
    ("type", typeAst.toJson),
    ("value", valueAst.toJson),
    ("node_count_type", Json.num typeAst.countNodes),
    ("node_count_value", Json.num valueAst.countNodes),
    ("was_truncated_type", Json.bool typeTruncated),
    ("was_truncated_value", Json.bool valueTruncated),
    ("lambda_core_type_tree", lambdaCoreTypeAst.toJson),
    ("lambda_core_value_tree", lambdaCoreValueAst.toJson),
    ("node_count_lambda_core_type", Json.num lambdaCoreTypeAst.countNodes),
    ("node_count_lambda_core_value", Json.num lambdaCoreValueAst.countNodes),
    ("was_truncated_lambda_core_type", Json.bool lambdaCoreTypeTruncated),
    ("was_truncated_lambda_core_value", Json.bool lambdaCoreValueTruncated),
    ("consts_type", Json.arr (constsType.map Json.str)),
    ("consts_value", Json.arr (constsValue.map Json.str)),
    ("n_consts_type", Json.num constsType.size),
    ("n_consts_value", Json.num constsValue.size),
    ("was_truncated_consts_type", Json.bool constsTypeTruncated),
    ("was_truncated_consts_value", Json.bool constsValueTruncated)
  ]
  let fields := match typePretty with
    | none => fields
    | some s => fields.push ("type_pretty", Json.str s)
  let fields := match valuePretty with
    | none => fields
    | some s => fields.push ("value_pretty", Json.str s)
  let fields :=
    match doc with
    | none => fields
    | some d => fields.push ("docString", Json.str d)
  Json.mkObj fields.toList

/-- Extract theorem declarations (type + proof term) as JSON objects. -/
def extractAllTheorems (opts : ExtractOptions := {}) (includePretty : Bool := true)
    (prettyMaxChars : Nat := 4000) : CoreM (Array Json) := do
  let env ← getEnv
  let mut out : Array Json := #[]
  let mut seen := 0

  let cSymbolGuessFor (n : Name) : String :=
    match Lean.getExportNameFor? env n with
    | some (.str .anonymous s) => s
    | some _ => n.mangle
    | none => if n == `main then "_lean_main" else n.mangle

  for (n, ci) in env.constants.toList do
    let ktd? : Option (String × String × Expr × Expr) :=
      match ci with
      | .thmInfo thm => some ("thm", "thm", thm.type, thm.value)
      | .defnInfo defn =>
        if opts.includeDefs then
          some ("def", "def", defn.type, defn.value)
        else
          none
      | _ => none
    match ktd? with
    | none => pure ()
    | some (kind, declClass, type, value) =>
      if keepConst env n opts then
        if let some mx := opts.maxTheorems then
          if seen ≥ mx then
            break
        let (typeAst, typeTrunc) := exprToAst type opts.maxNodes
        let (valueAst, valueTrunc) := exprToAst value opts.maxNodes
        let (lcTypeAst, lcTypeTrunc) := exprToLambdaCoreAst type opts.maxNodes
        let (lcValueAst, lcValueTrunc) := exprToLambdaCoreAst value opts.maxNodes
        let (constsType, constsTypeTrunc) := exprToConstList type opts.maxNodes opts.maxConstsPerDecl
        let (constsValue, constsValueTrunc) := exprToConstList value opts.maxNodes opts.maxConstsPerDecl
        let mod := moduleFor env n
        let cSymbolGuess := cSymbolGuessFor n
        let (typePretty, valuePretty) ←
          if !includePretty then
            pure (none, none)
          else
            let (pair, _) ← (do
              let tFmt ← PrettyPrinter.ppExpr type
              let vFmt ← PrettyPrinter.ppExpr value
              pure (some (truncateString tFmt.pretty prettyMaxChars),
                    some (truncateString vFmt.pretty prettyMaxChars)) : MetaM (Option String × Option String)).run {} {}
            pure pair
        out :=
          out.push
            (proofInfoToJson n mod kind declClass cSymbolGuess typeAst valueAst typeTrunc valueTrunc lcTypeAst lcValueAst lcTypeTrunc lcValueTrunc constsType constsValue
              constsTypeTrunc constsValueTrunc typePretty valuePretty none)
        seen := seen + 1
  return out

end HeytingLean.Embedding
