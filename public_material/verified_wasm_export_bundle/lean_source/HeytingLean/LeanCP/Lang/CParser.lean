import HeytingLean.LeanCP.Lang.CSyntax
import Lean.Data.Json

/-!
# LeanCP C Parser — JSON Deserializer

Deserializes a JSON representation of C AST (produced by an external C parser
such as pycparser) into LeanCP's `CExpr` / `CStmt` / `CFunSpec` types.

Follows the Aeneas/Charon pattern: use an external tool for parsing, JSON
for serialization, and Lean for deserialization + verification.

## JSON Schema

```json
{
  "tag": "binop",
  "op": "add",
  "left": {"tag": "var", "name": "x"},
  "right": {"tag": "intLit", "value": 1}
}
```
-/

namespace HeytingLean.LeanCP

open Lean Json

set_option linter.deprecated false

/-- Parse a BinOp from a string. -/
def parseBinOp : String → Except String BinOp
  | "add" => .ok .add
  | "sub" => .ok .sub
  | "mul" => .ok .mul
  | "div" => .ok .div
  | "mod" => .ok .mod
  | "eq" => .ok .eq
  | "ne" => .ok .ne
  | "lt" => .ok .lt
  | "le" => .ok .le
  | "gt" => .ok .gt
  | "ge" => .ok .ge
  | "and" => .ok .lAnd
  | "or" => .ok .lOr
  | "bitAnd" => .ok .bitAnd
  | "bitOr" => .ok .bitOr
  | "bitXor" => .ok .bitXor
  | "shl" => .ok .shl
  | "shr" => .ok .shr
  | "lAnd" => .ok .lAnd
  | "lOr" => .ok .lOr
  | s => .error s!"unknown BinOp: {s}"

/-- Parse a CType from JSON. -/
partial def parseCType : Json → Except String CType
  | .str "int" => .ok .int
  | .str "float" => .ok .float
  | .str "double" => .ok .double
  | .str "void" => .ok .void
  | .obj fields => do
      let tag ← match fields.find? "tag" with
        | some (.str s) => .ok s
        | _ => .error "CType: missing tag"
      match tag with
      | "intSized" => do
          let signedness ← match fields.find? "signedness" with
            | some (.str "signed") => .ok Signedness.Signed
            | some (.str "unsigned") => .ok Signedness.Unsigned
            | _ => .error "intSized: missing signedness"
          let size ← match fields.find? "size" with
            | some (.str "I8") => .ok IntSize.I8
            | some (.str "I16") => .ok IntSize.I16
            | some (.str "I32") => .ok IntSize.I32
            | some (.str "I64") => .ok IntSize.I64
            | _ => .error "intSized: missing size"
          .ok (.intSized signedness size)
      | "ptr" => do
          let inner ← match fields.find? "inner" with
            | some j => parseCType j
            | none => .ok CType.void
          .ok (.ptr inner)
      | "struct" => do
          let name ← match fields.find? "name" with
            | some (.str s) => .ok s
            | _ => .error "struct: missing name"
          .ok (.struct name)
      | "union" => do
          let name ← match fields.find? "name" with
            | some (.str s) => .ok s
            | _ => .error "union: missing name"
          .ok (.union name)
      | "enum" => do
          let name ← match fields.find? "name" with
            | some (.str s) => .ok s
            | _ => .error "enum: missing name"
          .ok (.enum name)
      | "typedef" => do
          let name ← match fields.find? "name" with
            | some (.str s) => .ok s
            | _ => .error "typedef: missing name"
          .ok (.typedef name)
      | _ => .error s!"unknown CType tag: {tag}"
  | _ => .error "CType: expected string or object"

/-- Parse a CExpr from JSON. -/
partial def parseCExpr : Json → Except String CExpr
  | .obj fields => do
      let tag ← match fields.find? "tag" with
        | some (.str s) => .ok s
        | _ => .error "CExpr: missing tag"
      match tag with
      | "var" => do
          let name ← match fields.find? "name" with
            | some (.str s) => .ok s
            | _ => .error "var: missing name"
          .ok (.var name)
      | "intLit" => do
          let v ← match fields.find? "value" with
            | some (.num n) => .ok n.mantissa
            | _ => .error "intLit: missing value"
          .ok (.intLit v)
      | "floatLit" => do
          let v ← match fields.find? "value" with
            | some (.num n) => .ok (Float.ofScientific n.mantissa.natAbs true n.exponent)
            | _ => .error "floatLit: missing value"
          .ok (.floatLit v)
      | "null" => .ok .null
      | "binop" => do
          let opStr ← match fields.find? "op" with
            | some (.str s) => .ok s
            | _ => .error "binop: missing op"
          let op ← parseBinOp opStr
          let left ← match fields.find? "left" with
            | some j => parseCExpr j
            | none => .error "binop: missing left"
          let right ← match fields.find? "right" with
            | some j => parseCExpr j
            | none => .error "binop: missing right"
          .ok (.binop op left right)
      | "deref" => do
          let inner ← match fields.find? "expr" with
            | some j => parseCExpr j
            | none => .error "deref: missing expr"
          .ok (.deref inner)
      | "addrOf" => do
          let name ← match fields.find? "name" with
            | some (.str s) => .ok s
            | _ => .error "addrOf: missing name"
          .ok (.addrOf name)
      | "fieldAccess" => do
          let obj ← match fields.find? "expr" with
            | some j => parseCExpr j
            | none => .error "fieldAccess: missing expr"
          let field ← match fields.find? "field" with
            | some (.str s) => .ok s
            | _ => .error "fieldAccess: missing field"
          .ok (.fieldAccess obj field)
      | _ => .error s!"unknown CExpr tag: {tag}"
  | _ => .error "CExpr: expected object"

/-- Parse a CStmt from JSON. -/
partial def parseCStmt : Json → Except String CStmt
  | .obj fields => do
      let tag ← match fields.find? "tag" with
        | some (.str s) => .ok s
        | _ => .error "CStmt: missing tag"
      match tag with
      | "skip" => .ok .skip
      | "ret" => do
          let e ← match fields.find? "expr" with
            | some j => parseCExpr j
            | none => .error "ret: missing expr"
          .ok (.ret e)
      | "assign" => do
          let lhs ← match fields.find? "lhs" with
            | some j => parseCExpr j
            | none => .error "assign: missing lhs"
          let rhs ← match fields.find? "rhs" with
            | some j => parseCExpr j
            | none => .error "assign: missing rhs"
          .ok (.assign lhs rhs)
      | "seq" => do
          let s1 ← match fields.find? "first" with
            | some j => parseCStmt j
            | none => .error "seq: missing first"
          let s2 ← match fields.find? "second" with
            | some j => parseCStmt j
            | none => .error "seq: missing second"
          .ok (.seq s1 s2)
      | "ite" => do
          let cond ← match fields.find? "cond" with
            | some j => parseCExpr j
            | none => .error "ite: missing cond"
          let th ← match fields.find? "then" with
            | some j => parseCStmt j
            | none => .error "ite: missing then"
          let el ← match fields.find? "else" with
            | some j => parseCStmt j
            | none => .ok .skip
          .ok (.ite cond th el)
      | "alloc" => do
          let name ← match fields.find? "name" with
            | some (.str s) => .ok s
            | _ => .error "alloc: missing name"
          let cells := match fields.find? "cells" with
            | some (.num n) => Int.toNat n.mantissa
            | _ => 1
          .ok (.alloc name cells)
      | "free" => do
          let e ← match fields.find? "expr" with
            | some j => parseCExpr j
            | none => .error "free: missing expr"
          let cells := match fields.find? "cells" with
            | some (.num n) => Int.toNat n.mantissa
            | _ => 1
          .ok (.free e cells)
      | _ => .error s!"unknown CStmt tag: {tag}"
  | _ => .error "CStmt: expected object"

end HeytingLean.LeanCP
