import Std
import HeytingLean.BountyHunter.Solc.YulObjectMini.Types

/-!
# HeytingLean.BountyHunter.Solc.YulObjectMini.Parse

Best-effort parser for Yul object syntax:
- `object "Name" { ... }`
- `code { ... }`
- `data "Name" hex"..."` or `data "Name" "..."`

This is intentionally conservative: unknown constructs are rejected.
Comments and string literals are handled when scanning for braces.
-/

namespace HeytingLean.BountyHunter.Solc.YulObjectMini

private def isWs (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c = '_' || c = '$'

private def isIdentChar (c : Char) : Bool :=
  isIdentStart c || c.isDigit

private def slice (src : String) (a b : Nat) : String :=
  (src.data.drop a |>.take (b - a)).asString

private partial def skipBlockCommentE (cs : Array Char) (i : Nat) : Except String Nat := do
  let mut j := i
  while j + 1 < cs.size do
    if cs[j]! = '*' && cs[j+1]! = '/' then
      return j + 2
    j := j + 1
  throw "unterminated block comment"

private partial def skipStringLitE (cs : Array Char) (i : Nat) : Except String Nat := do
  -- assumes cs[i] == '"'
  let mut j := i + 1
  while j < cs.size do
    let c := cs[j]!
    if c = '\\' then
      j := j + 2
    else if c = '"' then
      return j + 1
    else
      j := j + 1
  throw "unterminated string literal"

private partial def skipWsAndCommentsE (src : String) (i0 : Nat) : Except String Nat := do
  let cs := src.data.toArray
  let mut i := i0
  while i < cs.size do
    let c := cs[i]!
    if isWs c then
      i := i + 1
    else if i + 1 < cs.size && c = '/' && cs[i+1]! = '/' then
      -- line comment
      i := i + 2
      while i < cs.size && cs[i]! != '\n' do
        i := i + 1
    else if i + 1 < cs.size && c = '/' && cs[i+1]! = '*' then
      i := (← skipBlockCommentE cs (i + 2))
    else
      return i
  return i

private def startsWithAt (src : String) (i : Nat) (pat : String) : Bool :=
  Id.run do
    let cs := src.data
    let ps := pat.data
    if i + ps.length > cs.length then return false
    for j in [0:ps.length] do
      if cs[i + j]! != ps[j]! then return false
    return true

private def expectCharE (src : String) (i : Nat) (c : Char) (ctx : String) : Except String Nat := do
  let cs := src.data
  match cs[i]? with
  | some got =>
      if got = c then return i + 1 else throw s!"{ctx}: expected '{c}', got '{got}'"
  | none => throw s!"{ctx}: unexpected end of input"

private def parseIdentE (src : String) (i0 : Nat) : Except String (String × Nat) := do
  let cs := src.data
  match cs[i0]? with
  | none => throw "expected identifier, got EOF"
  | some c =>
      if !isIdentStart c then throw s!"expected identifier, got '{c}'"
      let mut i := i0 + 1
      while i < cs.length && isIdentChar cs[i]! do
        i := i + 1
      return (slice src i0 i, i)

private def parseStringLitE (src : String) (i0 : Nat) : Except String (String × Nat) := do
  let cs := src.data.toArray
  if i0 >= cs.size || cs[i0]! != '"' then
    throw "expected string literal"
  let mut out : Array Char := #[]
  let mut i := i0 + 1
  while i < cs.size do
    let c := cs[i]!
    if c = '"' then
      return (String.mk out.toList, i + 1)
    else if c = '\\' then
      if i + 1 >= cs.size then throw "unterminated string escape"
      out := out.push cs[i+1]!
      i := i + 2
    else
      out := out.push c
      i := i + 1
  throw "unterminated string literal"

private partial def extractBraceBlockE (src : String) (i0 : Nat) : Except String (String × Nat) := do
  -- Expects `src[i0] == '{'`. Returns (body, indexAfterClosingBrace).
  let cs := src.data.toArray
  if i0 >= cs.size || cs[i0]! != '{' then
    throw "internal error: extractBraceBlockE expects '{'"
  let mut depth : Nat := 1
  let mut i := i0 + 1
  let bodyStart := i
  let mut mode : Nat := 0 -- 0 normal, 1 line comment, 2 block comment, 3 string
  while i < cs.size do
    let c := cs[i]!
    if mode = 1 then
      if c = '\n' then mode := 0
      i := i + 1
    else if mode = 2 then
      if i + 1 < cs.size && c = '*' && cs[i+1]! = '/' then
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
      if i + 1 < cs.size && c = '/' && cs[i+1]! = '/' then
        mode := 1
        i := i + 2
      else if i + 1 < cs.size && c = '/' && cs[i+1]! = '*' then
        mode := 2
        i := i + 2
      else if c = '"' then
        mode := 3
        i := i + 1
      else if c = '{' then
        depth := depth + 1
        i := i + 1
      else if c = '}' then
        depth := depth - 1
        if depth = 0 then
          let body := slice src bodyStart i
          return (body, i + 1)
        i := i + 1
      else
        i := i + 1
  throw "unterminated brace block"

mutual
  private partial def parseItemsE (src : String) (i0 : Nat) : Except String (Array Item × Nat) := do
    let mut i := (← skipWsAndCommentsE src i0)
    let mut out : Array Item := #[]
    while i < src.length do
      i := (← skipWsAndCommentsE src i)
      if i >= src.length then break
      if startsWithAt src i "object" then
        let (it, j) ← parseObjectE src i
        out := out.push it
        i := j
      else if startsWithAt src i "code" then
        let (it, j) ← parseCodeE src i
        out := out.push it
        i := j
      else if startsWithAt src i "data" then
        let (it, j) ← parseDataE src i
        out := out.push it
        i := j
      else
        let preview := slice src i (Nat.min (i + 40) src.length)
        throw s!"unexpected token near: {preview}"
    return (out, i)

  private partial def parseObjectE (src : String) (i0 : Nat) : Except String (Item × Nat) := do
    let mut i := i0 + "object".length
    i := (← skipWsAndCommentsE src i)
    let (name, i1) ← parseStringLitE src i
    let i2 := (← skipWsAndCommentsE src i1)
    let i3 := (← expectCharE src i2 '{' "object")
    let (body, j) ← extractBraceBlockE src (i3 - 1)
    let (items, _) ← parseItemsE body 0
    return (.object name items, j)

  private partial def parseCodeE (src : String) (i0 : Nat) : Except String (Item × Nat) := do
    let mut i := i0 + "code".length
    i := (← skipWsAndCommentsE src i)
    let i1 := (← expectCharE src i '{' "code")
    let (body, j) ← extractBraceBlockE src (i1 - 1)
    return (.code body, j)

  private partial def parseDataE (src : String) (i0 : Nat) : Except String (Item × Nat) := do
    let mut i := i0 + "data".length
    i := (← skipWsAndCommentsE src i)
    let (name, i1) ← parseStringLitE src i
    let i2 := (← skipWsAndCommentsE src i1)
    -- value: hex"..." or "..."
    if startsWithAt src i2 "hex" then
      let i3 := i2 + "hex".length
      let i4 := (← skipWsAndCommentsE src i3)
      let (v, j) ← parseStringLitE src i4
      return (.data name (.hex v), j)
    else
      let (v, j) ← parseStringLitE src i2
      return (.data name (.str v), j)
end

def parseProgramE (src : String) : Except String Program := do
  let (items, _) ← parseItemsE src 0
  return { items := items }

end HeytingLean.BountyHunter.Solc.YulObjectMini
