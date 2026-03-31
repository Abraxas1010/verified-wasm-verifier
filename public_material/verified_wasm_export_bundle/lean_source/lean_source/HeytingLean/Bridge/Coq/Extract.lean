namespace HeytingLean.Bridge.Coq

/-- Placeholder for Coq s-expression AST nodes -/
inductive SExpr where
  | atom : String → SExpr
  | list : List SExpr → SExpr
  deriving Repr, Inhabited

/-- Whitespace used between tokens in a Coq-style S-expression. -/
def isSpace (c : Char) : Bool :=
  c.isWhitespace

/-- Trim leading whitespace. -/
def trimLeft (xs : List Char) : List Char :=
  xs.dropWhile isSpace

/-- Parse one atom token from a list of chars.

Atoms are maximal non-whitespace / non-delimiter spans.
-/
def parseAtom (xs : List Char) : Option (String × List Char) :=
  let rec go (ys : List Char) (acc : List Char) : List Char × List Char :=
    match ys with
    | [] => (acc.reverse, [])
    | c :: cs =>
      if isSpace c || c = '(' || c = ')' then
        (acc.reverse, ys)
      else
        go cs (c :: acc)
  match xs with
  | [] => none
  | c :: cs =>
    if c = '(' || c = ')' || isSpace c then none
    else
      let (tok, rest) := go cs [c]
      some (String.mk tok, rest)

/-- Parse an S-expression from a character list, requiring the entire input is consumed. -/
partial def parseSExprFromChars (xs : List Char) : Except String (SExpr × List Char) := do
  let xs' := trimLeft xs
  match xs' with
  | [] => throw "empty input"
  | '(' :: rest =>
    let rec parseList (acc : List SExpr) (ts : List Char) :
        Except String (List SExpr × List Char) := do
      let tsk := trimLeft ts
      match tsk with
      | [] => throw "unclosed list"
      | ')' :: cs =>
          pure (acc.reverse, cs)
      | _ =>
          let (x, cs) ← parseSExprFromChars tsk
          parseList (x :: acc) cs
    let (elts, rest') ← parseList [] rest
    pure (.list elts, rest')
  | ')' :: _ =>
    throw "unexpected closing parenthesis"
  | _ =>
    match parseAtom xs' with
    | none => throw "invalid atom"
    | some (tok, rest) => pure (.atom tok, rest)

/-- Parse an entire S-expression string. -/
def parseSExpr (input : String) : Except String SExpr := do
  let (expr, rest) ← parseSExprFromChars input.toList
  let rest' := trimLeft rest
  if rest'.isEmpty then pure expr else throw s!"trailing input: {String.mk rest'}"

/-- Normalize an S-expression into a linear Coq-like text form. -/
def extractTerm (sexpr : SExpr) : Except String String :=
  match sexpr with
  | .atom s => .ok s
  | .list xs => do
    let parts ← xs.mapM extractTerm
    pure s!"({String.intercalate " " parts})"

end HeytingLean.Bridge.Coq
