import Std

/-!
# HeytingLean.BountyHunter.AlgebraIR.SlotRef

Structured (but lightweight) representation of dynamic storage locations.

Design constraints:
- We keep `Effect.storageReadDyn/Effect.storageWriteDyn` as string payloads for now.
- Those payloads are normalized into a small “SlotRef expression language” so we can:
  - compare dynamic locations deterministically for CEI,
  - generate Foundry harnesses for common patterns.

This language is intentionally partial: unrecognized expressions remain `.raw` and
stay `OUT_OF_SCOPE` for certification/harnessing.
-/

namespace HeytingLean.BountyHunter.AlgebraIR

/-! A tiny subset of Yul-like expressions that we are willing to treat as “keys”
for mapping/array addressing and offsets.

We do *not* try to type-check these (address vs uint256); consumers must stay
conservative. -/
inductive SlotKey where
  | caller
  | this
  | nat (n : Nat)
  | ident (name : String)
  | raw (expr : String)
  deriving Repr, DecidableEq, Inhabited

inductive SlotOffset where
  | nat (n : Nat)
  | key (k : SlotKey)
  deriving Repr, DecidableEq, Inhabited

inductive SlotRef where
  | literal (slot : Nat)
  /-- `keccak256(abi.encode(key, base))` (mapping element). -/
  | mapping (base : SlotRef) (key : SlotKey)
  /-- `keccak256(abi.encode(base))` (dynamic-array data start, etc.). -/
  | keccak (base : SlotRef)
  /-- `base + offset` (whole-slot offsets, and array indices when supported). -/
  | add (base : SlotRef) (offset : SlotOffset)
  /-- A packed slice within a single storage slot. -/
  | packed (base : SlotRef) (byteOffset : Nat) (byteSize : Nat)
  | raw (expr : String)
  deriving Repr, DecidableEq, Inhabited

def slotKeyToYulExpr : SlotKey → String
  | .caller => "caller()"
  | .this => "address(this)"
  | .nat n => toString n
  | .ident s => s
  | .raw s => s

def slotOffsetToString : SlotOffset → String
  | .nat n => toString n
  | .key k => slotKeyToYulExpr k

def slotRefToString : SlotRef → String
  | .literal n => toString n
  | .mapping base key => s!"mapping_index_access({slotRefToString base},{slotKeyToYulExpr key})"
  | .keccak base => s!"keccak({slotRefToString base})"
  | .add base off => s!"add({slotRefToString base},{slotOffsetToString off})"
  | .packed base bo bs => s!"packed({slotRefToString base},{bo},{bs})"
  | .raw e => e

private def trimParens? (s : String) : Option String :=
  if s.startsWith "(" && s.endsWith ")" && s.length ≥ 2 then
    some (s.drop 1 |>.dropRight 1)
  else
    none

private def splitTopComma? (s : String) : Option (String × String) :=
  let rec go (cs : List Char) (i depth : Nat) : Option (String × String) :=
    match cs with
    | [] => none
    | c :: rest =>
        let depth :=
          if c = '(' then depth + 1
          else if c = ')' then depth - 1
          else depth
        if c = ',' && depth = 0 then
          some (s.take i, s.drop (i + 1))
        else
          go rest (i + 1) depth
  go s.data 0 0

private def parseNatEq? (s : String) : Option Nat :=
  s.trim.toNat?

private def isPlainIdent (s : String) : Bool :=
  let t := s.trim
  if t = "" then
    false
  else
    t.data.all (fun c =>
      c.isAlphanum || c = '_' || c = '$' || c = '.')

private def parseKey (s : String) : SlotKey :=
  let t := s.trim
  if t = "caller" || t = "caller()" then
    .caller
  else if t = "address(this)" || t = "this" then
    .this
  else
    match parseNatEq? t with
    | some n => .nat n
    | none =>
        if isPlainIdent t then
          .ident t
        else
          .raw t

private def parseOffset (s : String) : SlotOffset :=
  match parseNatEq? s with
  | some n => .nat n
  | none => .key (parseKey s)

partial def slotRefParse? (s : String) : Option SlotRef :=
  let t := s.trim
  match parseNatEq? t with
  | some n => some (.literal n)
  | none =>
    if t.startsWith "add(" && t.endsWith ")" then
      match trimParens? (t.drop 3) with
      | none => none
      | some inner =>
          match splitTopComma? inner with
          | none => none
          | some (lhs, rhs) =>
              match slotRefParse? lhs with
              | some b => some (SlotRef.add b (parseOffset rhs))
              | none => none
    else if t.startsWith "keccak(" && t.endsWith ")" then
      match trimParens? (t.drop 6) with
      | none => none
      | some inner =>
          slotRefParse? inner |>.map SlotRef.keccak
    else if t.startsWith "packed(" && t.endsWith ")" then
      match trimParens? (t.drop 6) with
      | none => none
      | some inner =>
          match splitTopComma? inner with
          | none => none
          | some (a, rest) =>
              match splitTopComma? rest with
              | none => none
              | some (b, c) =>
                  match slotRefParse? a, parseNatEq? b, parseNatEq? c with
                  | some base, some bo, some bs => some (.packed base bo bs)
                  | _, _, _ => none
    else if t.startsWith "mapping_index_access" then
      -- Parse both:
      -- `mapping_index_access(<base>,caller())`
      -- and solc helper strings like:
      -- `mapping_index_access_t_...(<base>,caller())`
      match t.splitOn "(" with
      | _fn :: rest =>
          let after := String.intercalate "(" rest
          if !after.endsWith ")" then
            none
          else
            let inner := after.dropRight 1
            match splitTopComma? inner with
            | none => none
            | some (a, b) =>
                match slotRefParse? a with
                | some base => some (SlotRef.mapping base (parseKey b))
                | none =>
                    -- Back-compat: allow `<base>` as a Nat literal.
                    parseNatEq? a |>.map (fun n => SlotRef.mapping (.literal n) (parseKey b))
      | _ => none
    else
      none

end HeytingLean.BountyHunter.AlgebraIR
