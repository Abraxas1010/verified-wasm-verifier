import HeytingLean.Meta.LeanTT0.Core

namespace HeytingLean.Meta.LeanTT0

open HeytingLean.Meta.LeanTT0

/-
  Minimal term parser supporting:
  - variables: identifiers [A-Za-z_][A-Za-z0-9_]*
  - (lam x. body)
  - (app f a)
-/

inductive Tok
  | lpar | rpar | dot | ident (s : String)
  deriving Inhabited

private def lexFuel (fuel : Nat) (xs : List Char) (acc : List Tok) : List Tok :=
  match fuel with
  | 0 => acc.reverse
  | fuel + 1 =>
      match xs with
      | [] => acc.reverse
      | c :: rest =>
          if c = '(' then lexFuel fuel rest (Tok.lpar :: acc) else
          if c = ')' then lexFuel fuel rest (Tok.rpar :: acc) else
          if c = '.' then lexFuel fuel rest (Tok.dot :: acc) else
          if c.isWhitespace then lexFuel fuel rest acc else
          let rec ident (ys : List Char) (buf : List Char) : (String × List Char) :=
            match ys with
            | [] => (String.mk buf.reverse, [])
            | d :: ds =>
                if d.isAlphanum || d = '_' then
                  ident ds (d :: buf)
                else
                  (String.mk buf.reverse, ys)
          let (w, rem) := ident (c :: rest) []
          lexFuel fuel rem (Tok.ident w :: acc)

def lex (xs : List Char) (acc : List Tok) : List Tok :=
  lexFuel (xs.length + 1) xs acc

private def pTermFuel : Nat → List Tok → Except String (Tm × List Tok)
  | 0, _ => .error "parse error: fuel exhausted"
  | _ + 1, Tok.ident v :: ts =>
      if v.data.all Char.isDigit then
        Except.ok (Tm.nat (String.toNat! v), ts)
      else if v = "add" then
        Except.ok (Tm.primAdd, ts)
      else
        Except.ok (Tm.var v, ts)
  | fuel + 1, Tok.lpar :: Tok.ident "lam" :: Tok.ident x :: Tok.dot :: ts =>
      match pTermFuel fuel ts with
      | .ok (body, Tok.rpar :: ts') => .ok (Tm.lam x body, ts')
      | _ => .error "parse error: expected body and )"
  | fuel + 1, Tok.lpar :: Tok.ident "app" :: ts =>
      match pTermFuel fuel ts with
      | .ok (f, ts1) =>
        match pTermFuel fuel ts1 with
        | .ok (a, Tok.rpar :: ts2) => .ok (Tm.app f a, ts2)
        | _ => .error "parse error: expected arg and )"
      | _ => .error "parse error: expected function term"
  | fuel + 1, Tok.lpar :: ts =>
      -- generic parenthesized application: (f a)
      match pTermFuel fuel ts with
      | .ok (f, ts1) =>
        match pTermFuel fuel ts1 with
        | .ok (a, Tok.rpar :: ts2) => .ok (Tm.app f a, ts2)
        | _ => .error "parse error: expected arg and )"
      | _ => .error "parse error: expected function term"
  | _, _ => .error "parse error: unexpected token"

def pTerm : List Tok → Except String (Tm × List Tok) :=
  fun ts => pTermFuel (ts.length + 1) ts

def parseTerm (s : String) : Except String Tm :=
  let toks := lex s.data []
  match pTerm toks with
  | .ok (t, []) => .ok t
  | .ok (_, _ :: _) => .error "parse error: trailing tokens"
  | .error e => .error e

end HeytingLean.Meta.LeanTT0
