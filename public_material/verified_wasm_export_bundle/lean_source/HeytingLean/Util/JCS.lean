import Lean
import Lean.Data.Json

/-!
# RFC 8785-style JSON canonicalization (JCS)

This module implements a deterministic, whitespace-free JSON serializer inspired by
RFC 8785 (JSON Canonicalization Scheme / JCS):

- Objects are serialized with **member names sorted** by the lexicographic order of their
  UTF-16 code unit arrays.
- Strings are escaped with the **minimal** set of JSON escapes:
  `\"`, `\\`, `\b`, `\t`, `\n`, `\f`, `\r`, and `\u00XX` for remaining control chars.
- Arrays preserve order.

Note: RFC 8785 specifies number formatting via ECMAScript's `ToString` on IEEE-754 binary64.
Here we implement a deterministic formatting for `Lean.JsonNumber` that matches the
ECMAScript "decimal vs exponent" cutoffs and produces a minimal decimal for the *decimal*
value represented by `JsonNumber` (mantissa × 10^-exponent). For projects that need strict
IEEE-754 canonicalization, restrict inputs to integers (the common case for our artifacts).
-/

namespace HeytingLean.Util.JCS

open Lean

/-! ## UTF-16 ordering for member names -/

private def utf16Units (s : String) : Array UInt16 :=
  Id.run do
    let mut out : Array UInt16 := #[]
    for c in s.toList do
      let n := c.val.toNat
      if n ≤ 0xFFFF then
        out := out.push (UInt16.ofNat n)
      else
        -- Encode as surrogate pair (n ∈ [0x10000, 0x10FFFF]).
        let x := n - 0x10000
        let hi := 0xD800 + (x / 0x400)
        let lo := 0xDC00 + (x % 0x400)
        out := out.push (UInt16.ofNat hi)
        out := out.push (UInt16.ofNat lo)
    return out

private def compareUtf16 (a b : String) : Ordering :=
  let aa := utf16Units a
  let bb := utf16Units b
  Id.run do
    let mut i : Nat := 0
    while i < aa.size && i < bb.size do
      let xa := aa[i]!.toNat
      let xb := bb[i]!.toNat
      if xa < xb then
        return Ordering.lt
      else if xb < xa then
        return Ordering.gt
      else
        i := i + 1
    if aa.size < bb.size then
      return Ordering.lt
    else if bb.size < aa.size then
      return Ordering.gt
    else
      return Ordering.eq

private def utf16Le (a b : String) : Bool :=
  match compareUtf16 a b with
  | .gt => false
  | _ => true

private def insertSorted (p : String × Json) (xs : List (String × Json)) : List (String × Json) :=
  match xs with
  | [] => [p]
  | q :: qs => if utf16Le p.fst q.fst then p :: xs else q :: insertSorted p qs

private def sortPairs : List (String × Json) → List (String × Json)
  | [] => []
  | p :: ps => insertSorted p (sortPairs ps)

/-! ## String escaping -/

private def hexDigit (n : Nat) : Char :=
  -- lower-case hex (0-9a-f)
  let n := n % 16
  if n < 10 then
    Char.ofNat ('0'.toNat + n)
  else
    Char.ofNat ('a'.toNat + (n - 10))

private def u00 (n : Nat) : String :=
  let hi := hexDigit (n / 16)
  let lo := hexDigit (n % 16)
  "\\u00" |>.push hi |>.push lo

private def escapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\x08' then "\\b"
  else if c = '\x09' then "\\t"
  else if c = '\x0a' then "\\n"
  else if c = '\x0c' then "\\f"
  else if c = '\x0d' then "\\r"
  else if c.val.toNat < 0x20 then
    u00 c.val.toNat
  else
    String.singleton c

private def renderString (s : String) : String :=
  Id.run do
    let mut acc := "\""
    for c in s.toList do
      acc := acc ++ escapeChar c
    acc := acc ++ "\""
    return acc

/-! ## Number formatting -/

private def natDigits (n : Nat) : Nat :=
  let rec loop (n digits : Nat) : Nat :=
    if n ≤ 9 then digits else loop (n / 10) (digits + 1)
  if n = 0 then 1 else loop n 1

private def trimTrailingZeros (s : String) : String :=
  s.dropRightWhile (fun c => c = '0')

private def takeChars (s : String) (n : Nat) : String :=
  String.mk (s.toList.take n)

private def dropChars (s : String) (n : Nat) : String :=
  String.mk (s.toList.drop n)

private def repeatChar (c : Char) (n : Nat) : String :=
  String.mk (List.replicate n c)

private def renderInt (i : Int) : String :=
  if i < 0 then "-" ++ toString i.natAbs else toString i.natAbs

private def renderJsonNumber (n : JsonNumber) : String :=
  let m := n.mantissa
  if m = 0 then
    "0"
  else
    let sign := if m < 0 then "-" else ""
    let mAbs := m.natAbs
    let digits := toString mAbs
    let d := digits.length
    let e := n.exponent
    -- scientific exponent = (d - 1) - e
    let sciExp : Int := (d - 1 : Nat) - (e : Nat)

    -- Decide between decimal and exponential representation using the ECMAScript cutoffs:
    --   use exponent form for abs(x) < 1e-6 or abs(x) ≥ 1e21.
    let useExp : Bool :=
      (sciExp < (-6 : Int)) || (sciExp ≥ (21 : Int))

    if useExp then
      let first := takeChars digits 1
      let rest := trimTrailingZeros (dropChars digits 1)
      let mant :=
        if rest.isEmpty then first else first ++ "." ++ rest
      let expSign := if sciExp ≥ 0 then "+" else "-"
      let expAbs := toString sciExp.natAbs
      sign ++ mant ++ "e" ++ expSign ++ expAbs
    else
      if e = 0 then
        sign ++ digits
      else if e < d then
        let splitAt := d - e
        let intPart := takeChars digits splitAt
        let fracPart := trimTrailingZeros (dropChars digits splitAt)
        if fracPart.isEmpty then
          sign ++ intPart
        else
          sign ++ intPart ++ "." ++ fracPart
      else
        let zeros := e - d
        let fracPart := trimTrailingZeros (repeatChar '0' zeros ++ digits)
        sign ++ "0." ++ fracPart

/-! ## Canonical JSON string -/

private def canonicalStringFuel : Nat → Json → String
  | 0, _ => "null" -- unreachable for well-formed inputs (fuel chosen from `sizeOf`)
  | Nat.succ fuel, j =>
      match j with
      | .null => "null"
      | .bool true => "true"
      | .bool false => "false"
      | .num n => renderJsonNumber n
      | .str s => renderString s
      | .arr elems =>
          let parts := elems.toList.map (canonicalStringFuel fuel)
          "[" ++ String.intercalate "," parts ++ "]"
      | .obj kvs =>
          let fields := sortPairs kvs.toList
          let parts :=
            fields.map (fun kv => renderString kv.fst ++ ":" ++ canonicalStringFuel fuel kv.snd)
          "{" ++ String.intercalate "," parts ++ "}"

def canonicalString (j : Json) : String :=
  -- The fuel is derived from the Lean JSON serialization length, which is a safe
  -- upper bound for the depth of the JSON tree in practice.
  canonicalStringFuel (j.compress.length + 1) j

end HeytingLean.Util.JCS
