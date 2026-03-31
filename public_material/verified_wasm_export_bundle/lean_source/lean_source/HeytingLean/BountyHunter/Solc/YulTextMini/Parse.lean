import Std
import HeytingLean.BountyHunter.Solc.YulTextMini.Types

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.Parse

Lexer + parser for a small Yul-text subset.

Goal: robustly extract enough structure/effects from Solidity `ir` / `irOptimized`
strings to drive Phase 1 checks (e.g. CEI), without pretending to be a complete
Yul parser.
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

inductive Tok where
  | ident (s : String)
  | nat (n : Nat)
  | str (s : String)
  | lparen | rparen | lbrace | rbrace | comma
  | assignColonEq  -- :=
  deriving Repr, DecidableEq, Inhabited

namespace Tok

def render : Tok → String
  | .ident s => s
  | .nat n => toString n
  | .str s => s!"\"{s}\""
  | .lparen => "("
  | .rparen => ")"
  | .lbrace => "{"
  | .rbrace => "}"
  | .comma => ","
  | .assignColonEq => ":="

end Tok

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c = '_' || c = '$'

private def isIdentChar (c : Char) : Bool :=
  isIdentStart c || c.isDigit

private def mkString (cs : List Char) : String :=
  String.mk cs

private def spanChars (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if p c then
        let (a, b) := spanChars p cs
        (c :: a, b)
      else
        ([], c :: cs)

private def dropLineComment : List Char → List Char
  | [] => []
  | '\n' :: cs => cs
  | _ :: cs => dropLineComment cs

private def dropBlockComment : List Char → Except String (List Char)
  | [] => throw "unterminated block comment"
  | '*' :: '/' :: cs => pure cs
  | _ :: cs => dropBlockComment cs

private def hexVal? (c : Char) : Option Nat :=
  if c.isDigit then
    some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then
    some (10 + (c.toNat - 'a'.toNat))
  else if 'A' ≤ c && c ≤ 'F' then
    some (10 + (c.toNat - 'A'.toNat))
  else
    none

private def parseHexNat? (hex : List Char) : Option Nat :=
  Id.run do
    let mut acc := 0
    for c in hex do
      match hexVal? c with
      | none => return none
      | some v => acc := acc * 16 + v
    return some acc

private def lexNat : List Char → Except String (Nat × List Char)
  | [] => throw "expected nat"
  | '0' :: ('x' :: cs) =>
      let (hex, rest) := spanChars (fun c => (hexVal? c).isSome) cs
      if hex.isEmpty then
        throw "invalid hex literal"
      else
        match parseHexNat? hex with
        | some n => pure (n, rest)
        | none => throw "invalid hex literal"
  | '0' :: ('X' :: cs) =>
      let (hex, rest) := spanChars (fun c => (hexVal? c).isSome) cs
      if hex.isEmpty then
        throw "invalid hex literal"
      else
        match parseHexNat? hex with
        | some n => pure (n, rest)
        | none => throw "invalid hex literal"
  | cs =>
      let (digits, rest) := spanChars (fun c => c.isDigit) cs
      match (mkString digits).toNat? with
      | some n => pure (n, rest)
      | none => throw "invalid nat literal"

private def lexStringLit : List Char → Except String (String × List Char)
  | '"' :: cs =>
      let rec go (acc : List Char) : List Char → Except String (String × List Char)
        | [] => throw "unterminated string literal"
        | '"' :: rest => pure (mkString acc.reverse, rest)
        | '\\' :: '"' :: rest => go ('"' :: acc) rest
        | '\\' :: '\\' :: rest => go ('\\' :: acc) rest
        | '\\' :: c :: rest => go (c :: acc) rest
        | c :: rest => go (c :: acc) rest
      go [] cs
  | _ => throw "expected string literal"

private def shouldSkipPunct (c : Char) : Bool :=
  -- These appear in Solidity IR around function signatures/metadata and are not
  -- needed for Phase 1 effect extraction. Skipping them makes lexing robust.
  c = ';' || c = ':' || c = '=' || c = '-' || c = '>' || c = '.' || c = '[' || c = ']'

partial def lex (src : String) : Except String (Array Tok) := do
  let rec dropWs (cs : List Char) (n : Nat := 0) : List Char × Nat :=
    match cs with
    | [] => ([], n)
    | c :: rest =>
        if c.isWhitespace then
          dropWs rest (n + 1)
        else
          (cs, n)
  let rec go : List Char → Array Tok → Except String (Array Tok)
    | [], toks => pure toks
    | c :: cs, toks =>
        if c.isWhitespace then
          go cs toks
        else
          match c, cs with
          | '/', '/' :: rest =>
              go (dropLineComment rest) toks
          | '/', '*' :: rest =>
              do
                let rest ← dropBlockComment rest
                go rest toks
          | '(', rest => go rest (toks.push .lparen)
          | ')', rest => go rest (toks.push .rparen)
          | '{', rest => go rest (toks.push .lbrace)
          | '}', rest => go rest (toks.push .rbrace)
          | ',', rest => go rest (toks.push .comma)
          | ':', '=' :: rest => go rest (toks.push .assignColonEq)
          | ':', rest =>
              -- Solidity IR sometimes prints `: =` with whitespace, which we
              -- still want to treat as `:=` for let/assignment parsing.
              let (rest', _) := dropWs rest
              match rest' with
              | '=' :: rest2 => go rest2 (toks.push .assignColonEq)
              | _ => go rest toks
          | '"', _ =>
              do
                let (s, rest) ← lexStringLit (c :: cs)
                go rest (toks.push (.str s))
          | c, rest =>
              if shouldSkipPunct c then
                go rest toks
              else if c.isDigit then
                do
                  let (n, rest) ← lexNat (c :: rest)
                  go rest (toks.push (.nat n))
              else if isIdentStart c then
                let (id, rest) := spanChars isIdentChar (c :: rest)
                go rest (toks.push (.ident (mkString id)))
              else
                throw s!"unexpected character: '{c}'"
  go src.data #[]

private def peek? (toks : Array Tok) (i : Nat) : Option Tok :=
  toks[i]?

private def expect (toks : Array Tok) (i : Nat) (t : Tok) (ctx : String) : Except String Nat := do
  match toks[i]? with
  | some got =>
      if got = t then
        pure (i + 1)
      else
        throw s!"expected {t.render} ({ctx}), got {got.render}"
  | none =>
      throw s!"unexpected end of input ({ctx})"

private def takeIdent (toks : Array Tok) (i : Nat) (ctx : String) : Except String (String × Nat) := do
  match toks[i]? with
  | some (.ident s) => pure (s, i + 1)
  | some other => throw s!"expected identifier ({ctx}), got {other.render}"
  | none => throw s!"unexpected end of input ({ctx})"

mutual
  private partial def parseExprE (toks : Array Tok) (i : Nat) : Except String (Expr × Nat) := do
    match toks[i]? with
    | some (.ident fn) =>
        match toks[i+1]? with
        | some .lparen =>
            -- call expression
            let (args, j2) ← parseParenArgsE toks (i + 1)
            return (.call fn args, j2)
        | _ =>
            if fn = "true" then
              return (.bool true, i + 1)
            else if fn = "false" then
              return (.bool false, i + 1)
            else
              return (.ident fn, i + 1)
    | some (.nat n) => pure (.nat n, i + 1)
    | some (.str s) => pure (.str s, i + 1)
    | some other => throw s!"expected expression, got {other.render}"
    | none => throw "unexpected end of input (expression)"

  private partial def parseParenArgsE (toks : Array Tok) (i : Nat) : Except String (Array Expr × Nat) := do
    let j ← expect toks i .lparen "argument list '('"
    if toks[j]? = some .rparen then
      return (#[], j + 1)
    let rec parseArgs (k : Nat) (acc : Array Expr) : Except String (Array Expr × Nat) := do
      let (a, k2) ← parseExprE toks k
      match toks[k2]? with
      | some .comma => parseArgs (k2 + 1) (acc.push a)
      | some .rparen => pure (acc.push a, k2 + 1)
      | some other => throw s!"expected ',' or ')' in args, got {other.render}"
      | none => throw "unexpected end of input in args"
    parseArgs j #[]
end

private def parseLitE (toks : Array Tok) (i : Nat) : Except String (Lit × Nat) := do
  match toks[i]? with
  | some (.nat n) => pure (.nat n, i + 1)
  | some (.str s) => pure (.str s, i + 1)
  | some (.ident "true") => pure (.bool true, i + 1)
  | some (.ident "false") => pure (.bool false, i + 1)
  | some other => throw s!"expected literal (case value), got {other.render}"
  | none => throw "unexpected end of input (case literal)"

mutual
  private partial def parseStmtsUntilRBraceE (toks : Array Tok) (i : Nat) :
      Except String (Array Stmt × Nat) := do
    let rec go (j : Nat) (out : Array Stmt) : Except String (Array Stmt × Nat) := do
      match toks[j]? with
      | none => pure (out, j)
      | some .rbrace => pure (out, j)
      | _ =>
          let (s, j2) ← parseStmtE toks j
          go j2 (out.push s)
    go i #[]

  private partial def parseStmtE (toks : Array Tok) (i : Nat) : Except String (Stmt × Nat) := do
    match toks[i]? with
    | some (.ident "let") =>
        let (name0, j0) ← takeIdent toks (i + 1) "let binding"
        let rec parseNames (j : Nat) (acc : Array String) : Except String (Array String × Nat) := do
          match toks[j]? with
          | some .comma =>
              let (nm, j2) ← takeIdent toks (j + 1) "let binding (additional name)"
              parseNames j2 (acc.push nm)
          | _ => pure (acc, j)
        let (names, j1) ← parseNames j0 #[name0]
        -- Solidity's IR/Yul occasionally emits `let x` / `let x, y` without an
        -- initializer. This has no observable effect for our Phase-1 analysis,
        -- so we treat it as an initializer to `0` and continue without consuming
        -- the next statement token.
        match toks[j1]? with
        | some .assignColonEq =>
            let (rhs, j3) ← parseExprE toks (j1 + 1)
            if names.size = 1 then
              pure (.let_ names[0]! rhs, j3)
            else
              pure (.letMany names rhs, j3)
        | _ =>
            let rhs : Expr := .nat 0
            if names.size = 1 then
              pure (.let_ names[0]! rhs, j1)
            else
              pure (.letMany names rhs, j1)
    | some (.ident "if") =>
        let (cond, j) ← parseExprE toks (i + 1)
        let j ← expect toks j .lbrace "if block"
        let (thenStmts, j) ← parseStmtsUntilRBraceE toks j
        let j ← expect toks j .rbrace "if block end"
        pure (.if_ cond thenStmts, j)
    | some (.ident "switch") =>
        let (scrut, j0) ← parseExprE toks (i + 1)
        let rec parseCases (j : Nat) (cases : Array (Lit × Array Stmt)) (def? : Option (Array Stmt)) :
            Except String (Array (Lit × Array Stmt) × Option (Array Stmt) × Nat) := do
          match toks[j]? with
          | some (.ident "case") =>
              let (lit, j1) ← parseLitE toks (j + 1)
              let j2 ← expect toks j1 .lbrace "case block"
              let (ss, j3) ← parseStmtsUntilRBraceE toks j2
              let j4 ← expect toks j3 .rbrace "case block end"
              parseCases j4 (cases.push (lit, ss)) def?
          | some (.ident "default") =>
              match def? with
              | some _ => throw "duplicate default in switch"
              | none =>
                  let j1 ← expect toks (j + 1) .lbrace "default block"
                  let (ss, j2) ← parseStmtsUntilRBraceE toks j1
                  let j3 ← expect toks j2 .rbrace "default block end"
                  parseCases j3 cases (some ss)
          | _ =>
              pure (cases, def?, j)
        let (cases, def?, j) ← parseCases j0 #[] none
        if cases.isEmpty && def?.isNone then
          throw "switch requires at least one case or default"
        pure (.switch_ scrut cases def?, j)
    | some (.ident "for") =>
        let j0 ← expect toks (i + 1) .lbrace "for init block"
        let (init, j1) ← parseStmtsUntilRBraceE toks j0
        let j2 ← expect toks j1 .rbrace "for init block end"
        let (cond, j3) ← parseExprE toks j2
        let j4 ← expect toks j3 .lbrace "for post block"
        let (post, j5) ← parseStmtsUntilRBraceE toks j4
        let j6 ← expect toks j5 .rbrace "for post block end"
        let j7 ← expect toks j6 .lbrace "for body block"
        let (body, j8) ← parseStmtsUntilRBraceE toks j7
        let j9 ← expect toks j8 .rbrace "for body block end"
        pure (.for_ init cond post body, j9)
    | some (.ident "break") => pure (.break, i + 1)
    | some (.ident "continue") => pure (.continue, i + 1)
    | some .lbrace =>
        let (stmts, j) ← parseStmtsUntilRBraceE toks (i + 1)
        let j ← expect toks j .rbrace "block end"
        pure (.block stmts, j)
    | some (.ident "return") =>
        match toks[i+1]? with
        | some .lparen =>
            let (args, j) ← parseParenArgsE toks (i + 1)
            pure (.return_ args, j)
        | _ =>
            pure (.return_ #[], i + 1)
    | some (.ident "revert") =>
        match toks[i+1]? with
        | some .lparen =>
            let (args, j) ← parseParenArgsE toks (i + 1)
            pure (.revert args, j)
        | _ =>
            pure (.revert #[], i + 1)
    | some (.ident "leave") => pure (.leave, i + 1)
    | some (.ident name) =>
      -- assignment (single or multi) or bare expression
      let rec gatherNames (j : Nat) (acc : Array String) : Except String (Array String × Nat) := do
        match toks[j]?, toks[j+1]? with
        | some .comma, some (.ident n2) =>
            gatherNames (j + 2) (acc.push n2)
        | _, _ =>
            return (acc, j)
      let (names, j) ← gatherNames (i + 1) #[name]
      match toks[j]? with
      | some .assignColonEq =>
          let (rhs, k) ← parseExprE toks (j + 1)
          if names.size = 1 then
            pure (.assign name rhs, k)
          else
            pure (.assignMany names rhs, k)
      | _ =>
          -- Not an assignment; parse as expression starting at the original position.
          let (e, k) ← parseExprE toks i
          pure (.expr e, k)
    | some _ =>
        let (e, j) ← parseExprE toks i
        pure (.expr e, j)
    | none =>
        throw "unexpected end of input (statement)"
end

def findFunctionBodyTokensE (src : String) (fnName : String) : Except String (Array Tok) := do
  let toks ← lex src
  let mut i : Nat := 0
  while i + 1 < toks.size do
    match toks[i]?, toks[i+1]? with
    | some (.ident "function"), some (.ident name) =>
        if name = fnName then
          -- Find the opening brace for the function body.
          let mut j := i + 2
          while j < toks.size && toks[j]? ≠ some .lbrace do
            j := j + 1
          if j ≥ toks.size then
            throw ("found function " ++ fnName ++ ", but no '{' body found")
          -- Capture body tokens until matching '}'
          let mut depth : Nat := 0
          let mut k := j
          let mut body : Array Tok := #[]
          while k < toks.size do
            match toks[k]? with
            | some .lbrace =>
                depth := depth + 1
                if depth > 1 then
                  body := body.push .lbrace
                pure ()
            | some .rbrace =>
                if depth = 0 then
                  throw "internal error: unmatched '}'"
                depth := depth - 1
                if depth = 0 then
                  return body
                body := body.push .rbrace
                pure ()
            | some t =>
                if depth > 0 then
                  body := body.push t
                pure ()
            | none =>
                pure ()
            k := k + 1
          throw s!"unterminated function body for {fnName}"
        else
          i := i + 2
    | _, _ =>
        i := i + 1
  throw s!"function not found: {fnName}"

def listFunctionNamesE (src : String) : Except String (Array String) := do
  let toks ← lex src
  let mut names : Array String := #[]
  let mut i : Nat := 0
  while i + 1 < toks.size do
    match toks[i]?, toks[i+1]? with
    | some (.ident "function"), some (.ident name) =>
        names := names.push name
        i := i + 2
    | _, _ =>
        i := i + 1
  -- deterministic sort/dedup
  let ys := names.qsort (fun a b => a < b)
  let mut out : Array String := #[]
  for x in ys do
    match out.back? with
    | none => out := out.push x
    | some y =>
        if x = y then continue else out := out.push x
  pure out

def parseFunctionBodyE (src : String) (fnName : String) : Except String (Array Stmt) := do
  let bodyToks ← findFunctionBodyTokensE src fnName
  let (stmts, i) ← parseStmtsUntilRBraceE bodyToks 0
  if i = bodyToks.size then
    pure stmts
  else
    throw "unexpected trailing tokens in function body"

def parseExprFromStringE (src : String) : Except String Expr := do
  let toks ← lex src
  let (e, i) ← parseExprE toks 0
  if i = toks.size then
    pure e
  else
    throw "unexpected trailing tokens in expression"

def parseStmtsFromStringE (src : String) : Except String (Array Stmt) := do
  let toks ← lex src
  let (stmts, i) ← parseStmtsUntilRBraceE toks 0
  if i = toks.size then
    pure stmts
  else
    throw "unexpected trailing tokens in statements"

end HeytingLean.BountyHunter.Solc.YulTextMini
