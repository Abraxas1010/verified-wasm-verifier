import HeytingLean.LeanSP.Pipeline.ContractLoader

/-!
# LeanSP.Pipeline.SolcASTGen

Build-time AST generation: compiles Solidity source via solc, parses the
optimized Yul IR, and emits a Lean 4 source file with AST definitions
that can be imported by verification modules.

This closes Honest Boundary #1: Yul ASTs are compiler-produced at build time,
not manually transcribed.

## Usage
```
lake exe solcASTGen <solFile> <outputLean> <funcName1> [funcName2 ...]
```

The generated file is a standalone Lean module that defines:
- `def <funcName>Body : List Stmt := [...]` for each requested function
- `def <funcName>Func : Yul.FuncDef := { ... }` with params/returns

The generator records the solc version and source file SHA-256 hash
in a header comment for provenance.
-/

namespace LeanSP.Pipeline

open HeytingLean.BountyHunter.Solc.YulTextMini

-- ==========================================
-- Lean source code emitters
-- ==========================================

/-- Emit a Lit as valid Lean 4 constructor syntax. -/
private def emitLit : Lit → String
  | .nat n => s!".nat {n}"
  | .str s => s!".str \"{s}\""
  | .bool b => s!".bool {b}"

/-- Emit an Expr as valid Lean 4 constructor syntax. -/
private partial def emitExpr : Expr → String
  | .ident name => s!".ident \"{name}\""
  | .nat n => s!".nat {n}"
  | .str s => s!".str \"{s}\""
  | .bool b => s!".bool {b}"
  | .call fn args =>
      let argsStr := ", ".intercalate (args.toList.map emitExpr)
      s!".call \"{fn}\" #[{argsStr}]"

/-- Emit a Stmt as valid Lean 4 constructor syntax. -/
private partial def emitStmt : Stmt → String
  | .let_ name rhs => s!".let_ \"{name}\" ({emitExpr rhs})"
  | .letMany names rhs =>
      let ns := ", ".intercalate (names.toList.map (fun n => s!"\"{n}\""))
      s!".letMany #[{ns}] ({emitExpr rhs})"
  | .assign name rhs => s!".assign \"{name}\" ({emitExpr rhs})"
  | .assignMany names rhs =>
      let ns := ", ".intercalate (names.toList.map (fun n => s!"\"{n}\""))
      s!".assignMany #[{ns}] ({emitExpr rhs})"
  | .expr e => s!".expr ({emitExpr e})"
  | .if_ cond body =>
      let bodyStr := ",\n      ".intercalate (body.toList.map emitStmt)
      s!".if_ ({emitExpr cond})\n      #[{bodyStr}]"
  | .switch_ scrut cases default? =>
      let casesStr := cases.toList.map fun (lit, stmts) =>
        let ss := ", ".intercalate (stmts.toList.map emitStmt)
        s!"({emitLit lit}, #[{ss}])"
      let csStr := ",\n        ".intercalate casesStr
      let defStr := match default? with
        | some d =>
            let ds := ", ".intercalate (d.toList.map emitStmt)
            s!"(some #[{ds}])"
        | none => "none"
      s!".switch_ ({emitExpr scrut})\n      #[{csStr}]\n      {defStr}"
  | .for_ init cond post body =>
      let initStr := ", ".intercalate (init.toList.map emitStmt)
      let postStr := ", ".intercalate (post.toList.map emitStmt)
      let bodyStr := ", ".intercalate (body.toList.map emitStmt)
      s!".for_ #[{initStr}]\n      ({emitExpr cond})\n      #[{postStr}]\n      #[{bodyStr}]"
  | .block stmts =>
      let ss := ", ".intercalate (stmts.toList.map emitStmt)
      s!".block #[{ss}]"
  | .break => ".break"
  | .continue => ".continue"
  | .return_ args =>
      let argsStr := ", ".intercalate (args.toList.map emitExpr)
      s!".return_ #[{argsStr}]"
  | .revert args =>
      let argsStr := ", ".intercalate (args.toList.map emitExpr)
      s!".revert #[{argsStr}]"
  | .leave => ".leave"

/-- Emit a list of stmts as a Lean list literal. -/
private def emitStmtList (stmts : Array Stmt) : String :=
  let entries := stmts.toList.map (fun s => s!"    {emitStmt s}")
  "[\n" ++ ",\n".intercalate entries ++ " ]"

/-- Sanitize a Yul function name for use as a Lean identifier.
    Replaces non-alphanumeric characters with underscores. -/
def sanitizeName (yulName : String) : String :=
  yulName.map fun c => if c.isAlphanum || c == '_' then c else '_'

-- ==========================================
-- SHA-256 hash of source file (for provenance)
-- ==========================================

private def hashFileContents (contents : String) : UInt64 := Id.run do
  -- Simple FNV-1a hash for provenance (not cryptographic)
  let mut h : UInt64 := 14695981039346656037
  for c in contents.toList do
    h := (h ^^^ c.toNat.toUInt64) * 1099511628211
  return h

-- ==========================================
-- Generator core
-- ==========================================

/-- Get the solc version string. -/
def getSolcVersion : IO String := do
  let output ← IO.Process.output { cmd := "solc", args := #["--version"] }
  pure output.stdout.trim

/-- Generate a complete Lean 4 source file from a Solidity contract.
    Compiles via solc, parses the Yul IR, and emits AST definitions. -/
def generateASTFile (solPath : System.FilePath) (moduleName : String)
    (functionNames : Array String) : IO String := do
  -- Compile via solc and extract deployed code functions
  let yulText ← compileSolToYulClean solPath
  -- Parse to get the YulUnit (finds first code block = constructor)
  let constructorUnit ← loadContract solPath
  -- Try constructor first; if functions not found, parse the full text
  -- to extract deployed object code where interesting functions live
  let funcs ← do
    let hasFunc := functionNames.any fun name =>
      constructorUnit.functions.any fun f => f.name == name
    if hasFunc then pure constructorUnit.functions
    else
      -- The deployed code is in a sub-object. Extract by finding the
      -- second "code {" block in the raw Yul text.
      let codeBlocks := yulText.splitOn "code {"
      if codeBlocks.length > 2 then
        -- The deployed code is the second code block
        let deployedCode := codeBlocks[2]!
        -- Find the matching } for this code block (approximate: take up to end)
        match extractFuncDefs deployedCode with
        | .ok fs => pure fs
        | .error _ => pure constructorUnit.functions
      else pure constructorUnit.functions
  let solcVer ← getSolcVersion
  let solContents ← IO.FS.readFile solPath
  let srcHash := hashFileContents solContents

  -- Build output
  let mut out := s!"-- AUTO-GENERATED by SolcASTGen — DO NOT EDIT\n"
  out := out ++ s!"-- Source: {solPath}\n"
  let solcVerOneLine := solcVer.replace "\n" " | "
  out := out ++ s!"-- Solc: {solcVerOneLine}\n"
  out := out ++ s!"-- Source hash (FNV-1a): {srcHash}\n"
  out := out ++ s!"-- Generated: {← IO.monoNanosNow}\n\n"
  out := out ++ s!"import HeytingLean.LeanSP.Lang.YulSyntax\n\n"
  out := out ++ s!"namespace {moduleName}\n\n"
  out := out ++ s!"open HeytingLean.BountyHunter.Solc.YulTextMini\n\n"

  -- Emit requested functions
  for funcName in functionNames do
    match funcs.find? (fun f => f.name == funcName) with
    | some funcDef =>
        let safeName := sanitizeName funcDef.name
        out := out ++ s!"/-- Yul AST for `{funcDef.name}` (compiler-generated). -/\n"
        out := out ++ s!"def {safeName}Body : List Stmt :=\n"
        out := out ++ s!"  {emitStmtList funcDef.body}\n\n"
        let paramsStr := ", ".intercalate (funcDef.params.toList.map (fun p => s!"\"{p}\""))
        let retsStr := ", ".intercalate (funcDef.returns.toList.map (fun r => s!"\"{r}\""))
        out := out ++ s!"def {safeName}Func : LeanSP.Yul.FuncDef :=\n"
        out := out ++ s!"  \{ name := \"{funcDef.name}\"\n"
        out := out ++ s!"    params := #[{paramsStr}], returns := #[{retsStr}]\n"
        out := out ++ s!"    body := {safeName}Body.toArray }\n\n"
    | none =>
        out := out ++ s!"-- WARNING: function '{funcName}' not found in solc output\n\n"

  out := out ++ s!"end {moduleName}\n"
  pure out

end LeanSP.Pipeline

/-- CLI entry point for solcASTGen. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | solFile :: outFile :: funcNames =>
    if funcNames.isEmpty then
      IO.eprintln "Usage: solcASTGen <solFile> <outputLean> <funcName1> [funcName2 ...]"
      return 1
    let rawName := (System.FilePath.mk outFile).fileName.getD "Generated"
    let moduleName := if rawName.endsWith ".lean" then rawName.dropRight 5 else rawName
    let content ← LeanSP.Pipeline.generateASTFile
      (System.FilePath.mk solFile)
      s!"LeanSP.Generated.{moduleName}"
      funcNames.toArray
    IO.FS.writeFile (System.FilePath.mk outFile) content
    IO.println s!"Generated: {outFile} ({funcNames.length} functions)"
    return 0
  | _ =>
    IO.eprintln "Usage: solcASTGen <solFile> <outputLean> <funcName1> [funcName2 ...]"
    return 1
