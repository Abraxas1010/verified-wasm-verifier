import Lean
import Lean.Data.Json
import Std
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.Solc.YulTextMini
import HeytingLean.BountyHunter.Solc.YulTextMini.Pretty
import HeytingLean.BountyHunter.Solc.YulTextMini.AlphaRename
import HeytingLean.BountyHunter.Solc.YulObjectMini
import HeytingLean.BountyHunter.AlgebraIR2.ANF

/-!
# HeytingLean.BountyHunter.AlgebraIR2.Codegen

Minimal “true AlgebraIR2 → codegen” spine (v0):

- Parse *function bodies* from a Solidity `ir` / `irOptimized` Yul object string
  into `YulTextMini.Stmt`s.
- Re-emit those bodies deterministically via `YulTextMini.Pretty`.
- Splice the canonicalized bodies back into the original IR text.
  We also apply a deterministic ANF normalization pass (after alpha-renaming) to
  reduce “structure borrowing” from solc’s formatting while keeping semantics.

This is intentionally coverage-driven:
- If we cannot parse a function body, we record a failure and (optionally) refuse
  to use the regenerated IR for semantic parity checks.
- We do *not* pretend to be a complete Yul parser.
- We keep the outer object wrapper and function headers verbatim.
-/

namespace HeytingLean.BountyHunter.AlgebraIR2

open Lean
open HeytingLean.BountyHunter.Solc

structure CodegenStats where
  version : String := "bh.algebrair2.codegen_stats.v0"
  functionsTotal : Nat := 0
  functionsParsed : Nat := 0
  codeBlocksTotal : Nat := 0
  codeBlocksParsed : Nat := 0
  failures : Array (String × String) := #[]
  deriving Repr, Inhabited

def codegenStatsToJson (s : CodegenStats) : Json :=
  Json.mkObj
    [ ("version", Json.str s.version)
    , ("functionsTotal", Json.num s.functionsTotal)
    , ("functionsParsed", Json.num s.functionsParsed)
    , ("codeBlocksTotal", Json.num s.codeBlocksTotal)
    , ("codeBlocksParsed", Json.num s.codeBlocksParsed)
    , ("failures",
        Json.arr <|
          s.failures.map (fun (p : String × String) =>
            Json.mkObj [("fn", Json.str p.1), ("error", Json.str p.2)]))
    ]

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c = '_' || c = '$'

private def isIdentChar (c : Char) : Bool :=
  isIdentStart c || c.isDigit

private def isWs (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

private def mkSpaces (n : Nat) : String :=
  String.mk (List.replicate n ' ')

private def lineIndentAt (src : String) (i : Nat) : Nat :=
  -- Count leading whitespace on the line containing position `i` (spaces+tabs).
  Id.run do
    let cs := src.data
    let mut j := i
    while j > 0 && cs[j-1]! != '\n' do
      j := j - 1
    let mut n : Nat := 0
    while j < cs.length do
      let c := cs[j]!
      if c = ' ' then
        n := n + 1
      else if c = '\t' then
        -- normalize tabs to 2 spaces (deterministic)
        n := n + 2
      else
        break
      j := j + 1
    return n

private def skipLineComment (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | '\n' :: rest => rest
  | _ :: rest => skipLineComment rest

private partial def skipBlockComment : List Char → Except String (List Char)
  | [] => throw "unterminated block comment"
  | '*' :: '/' :: rest => pure rest
  | _ :: rest => skipBlockComment rest

private partial def skipStringLit : List Char → Except String (List Char)
  | [] => throw "unterminated string literal"
  | '"' :: rest => pure rest
  | '\\' :: '"' :: rest => skipStringLit rest
  | '\\' :: '\\' :: rest => skipStringLit rest
  | '\\' :: _ :: rest => skipStringLit rest
  | _ :: rest => skipStringLit rest

private def slice (src : String) (a b : Nat) : String :=
  (src.data.drop a |>.take (b - a)).asString

structure FnSpan where
  name : String
  braceIndent : Nat
  bodyStart : Nat
  bodyEnd : Nat
  deriving Repr, Inhabited

private def findFunctionSpansE (src : String) : Except String (Array FnSpan) := do
  let cs := src.data
  let kw : List Char := "function".data
  let kwLen := kw.length

  let startsWithAt (i : Nat) (pat : List Char) : Bool :=
    Id.run do
      if i + pat.length > cs.length then return false
      let mut j := 0
      for c in pat do
        if cs[i + j]! != c then return false
        j := j + 1
      return true

  let mut out : Array FnSpan := #[]
  let mut i : Nat := 0
  let mut mode : Nat := 0 -- 0 normal, 1 line comment, 2 block comment, 3 string

  while i < cs.length do
    let c := cs[i]!
    if mode = 1 then
      if c = '\n' then mode := 0
      i := i + 1
    else if mode = 2 then
      if i + 1 < cs.length && c = '*' && cs[i+1]! = '/' then
        mode := 0
        i := i + 2
      else
        i := i + 1
    else if mode = 3 then
      if c = '\\' then
        i := i + 2
      else if c = '"' then
        mode := 0
        i := i + 1
      else
        i := i + 1
    else
      if i + 1 < cs.length && c = '/' && cs[i+1]! = '/' then
        mode := 1
        i := i + 2
      else if i + 1 < cs.length && c = '/' && cs[i+1]! = '*' then
        mode := 2
        i := i + 2
      else if c = '"' then
        mode := 3
        i := i + 1
      else if startsWithAt i kw then
        let prevOk := if i = 0 then true else !isIdentChar cs[i-1]!
        let nextOk := if i + kwLen >= cs.length then true else !isIdentChar cs[i + kwLen]!
        if prevOk && nextOk then
          -- Parse function name.
          let mut j := i + kwLen
          while j < cs.length && isWs cs[j]! do
            j := j + 1
          if j >= cs.length || !isIdentStart cs[j]! then
            i := i + 1
          else
            let mut k := j
            while k < cs.length && isIdentChar cs[k]! do
              k := k + 1
            let name := slice src j k
            -- Find opening brace of the body (skip over signature).
            let mut m := k
            let mut depthParen : Nat := 0
            let mut modeSig : Nat := 0 -- 0 normal, 1 line, 2 block, 3 string
            while m < cs.length do
              let ch := cs[m]!
              if modeSig = 1 then
                if ch = '\n' then modeSig := 0
                m := m + 1
              else if modeSig = 2 then
                if m + 1 < cs.length && ch = '*' && cs[m+1]! = '/' then
                  modeSig := 0
                  m := m + 2
                else
                  m := m + 1
              else if modeSig = 3 then
                if ch = '\\' then
                  m := m + 2
                else if ch = '"' then
                  modeSig := 0
                  m := m + 1
                else
                  m := m + 1
              else
                if m + 1 < cs.length && ch = '/' && cs[m+1]! = '/' then
                  modeSig := 1
                  m := m + 2
                else if m + 1 < cs.length && ch = '/' && cs[m+1]! = '*' then
                  modeSig := 2
                  m := m + 2
                else if ch = '"' then
                  modeSig := 3
                  m := m + 1
                else if ch = '(' then
                  depthParen := depthParen + 1
                  m := m + 1
                else if ch = ')' then
                  if depthParen > 0 then depthParen := depthParen - 1
                  m := m + 1
                else if ch = '{' && depthParen = 0 then
                  break
                else
                  m := m + 1
            if m >= cs.length || cs[m]! != '{' then
              throw ("function " ++ name ++ ": could not find '{' body")
            let braceIndent := lineIndentAt src m
            let bodyStart := m + 1
            -- Find matching closing brace.
            let mut depthBrace : Nat := 1
            let mut n := m + 1
            let mut modeBody : Nat := 0
            while n < cs.length do
              let ch := cs[n]!
              if modeBody = 1 then
                if ch = '\n' then modeBody := 0
                n := n + 1
              else if modeBody = 2 then
                if n + 1 < cs.length && ch = '*' && cs[n+1]! = '/' then
                  modeBody := 0
                  n := n + 2
                else
                  n := n + 1
              else if modeBody = 3 then
                if ch = '\\' then
                  n := n + 2
                else if ch = '"' then
                  modeBody := 0
                  n := n + 1
                else
                  n := n + 1
              else
                if n + 1 < cs.length && ch = '/' && cs[n+1]! = '/' then
                  modeBody := 1
                  n := n + 2
                else if n + 1 < cs.length && ch = '/' && cs[n+1]! = '*' then
                  modeBody := 2
                  n := n + 2
                else if ch = '"' then
                  modeBody := 3
                  n := n + 1
                else if ch = '{' then
                  depthBrace := depthBrace + 1
                  n := n + 1
                else if ch = '}' then
                  depthBrace := depthBrace - 1
                  if depthBrace = 0 then
                    out := out.push { name := name, braceIndent := braceIndent, bodyStart := bodyStart, bodyEnd := n }
                    i := n + 1
                    break
                  n := n + 1
                else
                  n := n + 1
            if depthBrace != 0 then
              throw s!"function {name}: unterminated body"
        else
          i := i + 1
      else
        i := i + 1
  return out

def canonicalizeFunctionBodiesE (ir : String) : Except String (String × CodegenStats) := do
  let spans ← findFunctionSpansE ir
  let mut stats : CodegenStats := { functionsTotal := spans.size }
  let mut out : String := ""
  let mut prev : Nat := 0
  for sp in spans do
    out := out ++ slice ir prev sp.bodyStart
    let body := slice ir sp.bodyStart sp.bodyEnd
    match YulTextMini.parseStmtsFromStringE body with
    | .ok ss =>
        stats := { stats with functionsParsed := stats.functionsParsed + 1 }
        let ss0 := HeytingLean.BountyHunter.Solc.YulTextMini.alphaRename ss
        let ss ←
          match HeytingLean.BountyHunter.AlgebraIR2.anfStmts ss0 with
          | .ok ssAnf => pure ssAnf
          | .error e => do
              stats := { stats with failures := stats.failures.push (sp.name, s!"ANF: {e}") }
              pure ss0
        let inner := YulTextMini.stmtsToString ss (sp.braceIndent + 2)
        out := out ++ "\n" ++ inner ++ "\n" ++ mkSpaces sp.braceIndent
    | .error e =>
        stats := { stats with failures := stats.failures.push (sp.name, e) }
        out := out ++ body
    prev := sp.bodyEnd
  out := out ++ slice ir prev ir.length
  return (out, stats)

private partial def canonicalizeCodeBlocks (it : YulObjectMini.Item) (stats : CodegenStats) :
    Except String (YulObjectMini.Item × CodegenStats) := do
  match it with
  | .code body =>
      let stats := { stats with codeBlocksTotal := stats.codeBlocksTotal + 1 }
      match canonicalizeFunctionBodiesE body with
      | .error e =>
          let stats := { stats with failures := stats.failures.push ("code", e) }
          return (.code body, stats)
      | .ok (body2, st2) =>
          let stats :=
            { stats with
              codeBlocksParsed := stats.codeBlocksParsed + 1
              functionsTotal := stats.functionsTotal + st2.functionsTotal
              functionsParsed := stats.functionsParsed + st2.functionsParsed
              failures := stats.failures ++ st2.failures
            }
          return (.code body2, stats)
  | .data n v => return (.data n v, stats)
  | .object name items =>
      let mut stats := stats
      let mut out : Array YulObjectMini.Item := #[]
      for x in items do
        let (y, st) ← canonicalizeCodeBlocks x stats
        out := out.push y
        stats := st
      return (.object name out, stats)

def canonicalizeYulObjectE (ir : String) : Except String (String × CodegenStats) := do
  let prog ← YulObjectMini.parseProgramE ir
  let mut stats : CodegenStats := {}
  let mut outItems : Array YulObjectMini.Item := #[]
  for it in prog.items do
    let (it2, st) ← canonicalizeCodeBlocks it stats
    outItems := outItems.push it2
    stats := st
  let prog2 : YulObjectMini.Program := { prog with items := outItems }
  let out := YulObjectMini.programToCanonicalString prog2
  return (out, stats)

end HeytingLean.BountyHunter.AlgebraIR2
