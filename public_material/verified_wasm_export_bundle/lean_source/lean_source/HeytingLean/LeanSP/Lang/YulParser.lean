import HeytingLean.LeanSP.Lang.YulSyntax
import HeytingLean.BountyHunter.Solc.YulTextMini.Parse
import HeytingLean.BountyHunter.Solc.YulObjectMini.Parse

/-!
# LeanSP.Lang.YulParser

Extends the existing YulTextMini parser to extract full function signatures
(parameter and return variable names) needed for value-level operational semantics.

Uses ONLY public APIs from YulTextMini.Parse:
- `lex` — tokenization
- `listFunctionNamesE` — discover function names
- `parseFunctionBodyE` — parse function body statements
- `parseStmtsFromStringE` — parse statement sequences from strings
-/

namespace LeanSP.Pipeline

open HeytingLean.BountyHunter.Solc

/-- Extract parameter names from a token stream starting right after `(`.
    Returns `(params, indexAfterRparen)`. -/
private def gatherParamsE (toks : Array YulTextMini.Tok) (start : Nat) :
    Except String (Array String × Nat) := do
  match toks[start]? with
  | some .rparen => return (#[], start + 1)
  | _ =>
    let mut j := start
    let mut params : Array String := #[]
    while j < toks.size do
      match toks[j]? with
      | some (.ident p) =>
          params := params.push p
          match toks[j + 1]? with
          | some .comma => j := j + 2
          | some .rparen => return (params, j + 2)
          | _ => throw s!"unexpected token after param '{p}'"
      | some other => throw s!"expected param name, got {other.render}"
      | none => throw "unexpected end of input in params"
    throw "unterminated parameter list"

/-- Extract return variable names from token stream starting right after `)`.
    The Yul `->` arrow is swallowed by the lexer (both `-` and `>` are in
    `shouldSkipPunct`), so returns appear as bare identifiers before `{`.
    Returns `(returns, indexOfLbrace)`. -/
private def gatherReturnsE (toks : Array YulTextMini.Tok) (start : Nat) :
    Except String (Array String × Nat) := do
  match toks[start]? with
  | some .lbrace => return (#[], start)
  | _ =>
    let mut j := start
    let mut rets : Array String := #[]
    while j < toks.size do
      match toks[j]? with
      | some (.ident r) =>
          rets := rets.push r
          match toks[j + 1]? with
          | some .comma => j := j + 2
          | some .lbrace => return (rets, j + 1)
          | _ => return (rets, j + 1)
      | some .lbrace => return (rets, j)
      | _ => j := j + 1
    throw "unterminated return variable list"

/-- Find the index after the matching `}` for a `{` at position `lbraceIdx`. -/
private def findMatchingBrace (toks : Array YulTextMini.Tok) (lbraceIdx : Nat) : Nat := Id.run do
  let mut depth : Nat := 0
  let mut j := lbraceIdx
  while j < toks.size do
    match toks[j]? with
    | some .lbrace => depth := depth + 1; j := j + 1
    | some .rbrace =>
        depth := depth - 1
        if depth = 0 then return j + 1
        j := j + 1
    | _ => j := j + 1
  return j

/-- Extract parameter/return signature for a named function from a lexed token stream. -/
private def extractSignatureE (toks : Array YulTextMini.Tok) (fnName : String) :
    Except String (Array String × Array String) := do
  let mut i : Nat := 0
  while i + 1 < toks.size do
    match toks[i]?, toks[i + 1]? with
    | some (.ident "function"), some (.ident name) =>
        if name = fnName then
          match toks[i + 2]? with
          | some .lparen =>
              let (params, afterRparen) ← gatherParamsE toks (i + 3)
              let (rets, _) ← gatherReturnsE toks afterRparen
              return (params, rets)
          | _ => throw s!"expected '(' after function {fnName}"
        else
          i := i + 2
    | _, _ => i := i + 1
  throw s!"function signature not found: {fnName}"

/-- Extract all function definitions from Yul source code body.
    Uses public YulTextMini APIs for body parsing + custom signature extraction. -/
def extractFuncDefs (codeBody : String) :
    Except String (Array Yul.FuncDef) := do
  let names ← YulTextMini.listFunctionNamesE codeBody
  let toks ← YulTextMini.lex codeBody
  let mut funcs : Array Yul.FuncDef := #[]
  for name in names do
    let body ← YulTextMini.parseFunctionBodyE codeBody name
    let (params, rets) ← extractSignatureE toks name
    funcs := funcs.push { name, params, returns := rets, body }
  return funcs

/-- Extract top-level statements (non-function code) from Yul code body.
    Identifies function definition spans in the token stream, removes them,
    reconstructs the remaining tokens as a string, and re-parses. -/
def extractTopLevelStmts (codeBody : String) :
    Except String (Array Yul.Stmt) := do
  let toks ← YulTextMini.lex codeBody
  -- Find function definition spans
  let mut funcSpans : Array (Nat × Nat) := #[]
  let mut i : Nat := 0
  while i + 1 < toks.size do
    match toks[i]?, toks[i + 1]? with
    | some (.ident "function"), some (.ident _) =>
        let endIdx := findMatchingBrace toks (i)
        -- findMatchingBrace finds the { of the body, but we started at 'function'
        -- We need to skip past the whole function def to the closing }
        -- Let's find the first { after i, then find its matching }
        let mut k := i + 2
        while k < toks.size do
          match toks[k]? with
          | some .lbrace =>
              let bodyEnd := findMatchingBrace toks k
              funcSpans := funcSpans.push (i, bodyEnd)
              i := bodyEnd
              k := toks.size  -- break inner loop
          | _ => k := k + 1
    | _, _ => i := i + 1
  -- Collect non-function tokens
  let mut topToks : Array String := #[]
  for j in [:toks.size] do
    let inFunc := funcSpans.any (fun (s, e) => s ≤ j && j < e)
    if !inFunc then
      match toks[j]? with
      | some t => topToks := topToks.push t.render
      | none => pure ()
  if topToks.isEmpty then return #[]
  let tokStr := " ".intercalate topToks.toList
  YulTextMini.parseStmtsFromStringE tokStr

/-- Navigate a YulObjectMini item tree to find the first code body string. -/
partial def findCodeBody : YulObjectMini.Item → Option String
  | .code body => some body
  | .object _ items => items.findSome? findCodeBody
  | .data _ _ => none

/-- Parse raw `solc --ir-optimized` output into a YulUnit.
    Pipeline: raw text → YulObjectMini.parseProgramE → find code body →
    extract functions + top-level statements. -/
def parseYulText (yulText : String) : Except String Yul.YulUnit := do
  let program ← YulObjectMini.parseProgramE yulText
  let objectName := match program.items[0]? with
    | some (.object name _) => name
    | _ => "unknown"
  let codeBody ← match program.items.findSome? findCodeBody with
    | some body => pure body
    | none => throw "no code block found in Yul object"
  let funcs ← extractFuncDefs codeBody
  let topStmts ← extractTopLevelStmts codeBody
  return { objectName, topLevelStmts := topStmts, functions := funcs }

/-- Parse a Yul code body string directly (skipping object wrapper parsing).
    Useful for testing with raw Yul code. -/
def parseYulCodeBody (codeBody : String) :
    Except String (Array Yul.FuncDef × Array Yul.Stmt) := do
  let funcs ← extractFuncDefs codeBody
  let topStmts ← extractTopLevelStmts codeBody
  return (funcs, topStmts)

end LeanSP.Pipeline
