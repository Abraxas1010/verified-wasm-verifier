import HeytingLean.LeanCP.Lang.CDecl

/-!
# LeanCP C Emission

Pretty-printer for the LeanCP-owned C AST (`CType`, `CExpr`, `CStmt`,
`CFunDecl`, `CProgramDecl`) to concrete C source text.

Conventions adapted from `HeytingLean.C.Emit`:
- 2-space indentation
- identifiers sanitized to `[A-Za-z0-9_]`
- expressions parenthesized for operator-precedence safety
- deterministic output (no IO, no randomness)
-/

namespace HeytingLean.LeanCP.CEmit

private def indent (n : Nat) : String :=
  String.intercalate "" (List.replicate (2 * n) " ")

private def paren (s : String) : String := s!"({s})"

private def sanitizeIdent (s : String) : String :=
  let s' := s.map (fun c => if c.isAlphanum || c = '_' then c else '_')
  if s'.isEmpty then "_empty" else s'

/-- Render an `IntSize` as its C type keyword fragment. -/
def intSizeStr : IntSize → String
  | .I8  => "int8_t"
  | .I16 => "int16_t"
  | .I32 => "int32_t"
  | .I64 => "int64_t"

/-- Render a `Signedness` + `IntSize` pair. -/
def signedIntStr : Signedness → IntSize → String
  | .Signed, sz   => intSizeStr sz
  | .Unsigned, sz => "u" ++ intSizeStr sz

/-- Render a `CType` as a C type string. For pointer/array/funcPtr types the
    declarator syntax is split: this returns the specifier part and a suffix
    function is not needed because we emit pointer-to-T as `T*`. -/
partial def typeStr : CType → String
  | .int            => "int"
  | .intSized sg sz => signedIntStr sg sz
  | .float          => "float"
  | .double         => "double"
  | .ptr inner      => typeStr inner ++ "*"
  | .array inner n  => typeStr inner ++ s!"[{n}]"
  | .funcPtr ret args =>
      let argStrs := args.map typeStr
      typeStr ret ++ " (*)(" ++ String.intercalate ", " argStrs ++ ")"
  | .struct name    => "struct " ++ sanitizeIdent name
  | .union name     => "union " ++ sanitizeIdent name
  | .enum name      => "enum " ++ sanitizeIdent name
  | .typedef name   => sanitizeIdent name
  | .void           => "void"

/-- Render a `BinOp` as its C operator token. -/
def binOpStr : BinOp → String
  | .add    => "+"
  | .sub    => "-"
  | .mul    => "*"
  | .div    => "/"
  | .mod    => "%"
  | .eq     => "=="
  | .ne     => "!="
  | .lt     => "<"
  | .le     => "<="
  | .gt     => ">"
  | .ge     => ">="
  | .and    => "&&"
  | .or     => "||"
  | .bitAnd => "&"
  | .bitOr  => "|"
  | .bitXor => "^"
  | .shl    => "<<"
  | .shr    => ">>"
  | .lAnd   => "&&"
  | .lOr    => "||"

/-- Render a `CExpr` as a C expression string. -/
partial def exprStr : CExpr → String
  | .var x            => sanitizeIdent x
  | .intLit n         => toString n
  | .floatLit v       => toString v
  | .null             => "NULL"
  | .sizeOf ty        => s!"sizeof({typeStr ty})"
  | .cast ty e        => paren (s!"{paren (typeStr ty)}{exprStr e}")
  | .binop op e1 e2   => paren s!"{exprStr e1} {binOpStr op} {exprStr e2}"
  | .deref e          => s!"(*{exprStr e})"
  | .arrayAccess a i  => s!"{exprStr a}[{exprStr i}]"
  | .addrOf x         => s!"(&{sanitizeIdent x})"
  | .fieldAccess e f  => s!"{exprStr e}->{sanitizeIdent f}"
  | .call fn args     =>
      let argStrs := args.map exprStr
      s!"{sanitizeIdent fn}({String.intercalate ", " argStrs})"

/-- Render a `CStmt` as a list of indented C source lines. -/
partial def stmtLines (n : Nat) : CStmt → List String
  | .skip => []
  | .assign lhs rhs =>
      [s!"{indent n}{exprStr lhs} = {exprStr rhs};"]
  | .seq s1 s2 =>
      stmtLines n s1 ++ stmtLines n s2
  | .ite cond th el =>
      let hd := s!"{indent n}if ({exprStr cond}) " ++ "{"
      let mid := s!"{indent n}" ++ "} else {"
      let tl := s!"{indent n}" ++ "}"
      [hd] ++ stmtLines (n + 1) th ++ [mid] ++ stmtLines (n + 1) el ++ [tl]
  | .whileInv cond _inv body =>
      let hd := s!"{indent n}while ({exprStr cond}) " ++ "{"
      let tl := s!"{indent n}" ++ "}"
      [hd] ++ stmtLines (n + 1) body ++ [tl]
  | .block decls body =>
      let hd := s!"{indent n}" ++ "{"
      let declLines := decls.map fun (x, ty) =>
        s!"{indent (n + 1)}{typeStr ty} {sanitizeIdent x} = 0;"
      let tl := s!"{indent n}" ++ "}"
      [hd] ++ declLines ++ stmtLines (n + 1) body ++ [tl]
  | .switch scrut tag caseBody default =>
      let hd := s!"{indent n}if ({exprStr scrut} == {tag}) " ++ "{"
      let mid := s!"{indent n}" ++ "} else {"
      let tl := s!"{indent n}" ++ "}"
      [hd] ++ stmtLines (n + 1) caseBody ++ [mid] ++ stmtLines (n + 1) default ++ [tl]
  | .forLoop init cond step body =>
      -- Emit as init; while (cond) { body; step; }
      stmtLines n init ++
      let hd := s!"{indent n}while ({exprStr cond}) " ++ "{"
      let tl := s!"{indent n}" ++ "}"
      [hd] ++ stmtLines (n + 1) body ++ stmtLines (n + 1) step ++ [tl]
  | .break =>
      [s!"{indent n}break;"]
  | .continue =>
      [s!"{indent n}continue;"]
  | .ret e =>
      [s!"{indent n}return {exprStr e};"]
  | .alloc x cells =>
      [s!"{indent n}{sanitizeIdent x} = malloc({cells} * sizeof(int));"]
  | .free e cells =>
      [s!"{indent n}free({exprStr e}); /* {cells} cells */"]
  | .decl x ty =>
      [s!"{indent n}{typeStr ty} {sanitizeIdent x};"]

/-- Emit a parameter declaration. -/
def paramStr (p : String × CType) : String :=
  s!"{typeStr p.2} {sanitizeIdent p.1}"

/-- Emit a `CFunDecl` as a complete C function definition. -/
def funDecl (f : CFunDecl) : String :=
  let paramsStr := String.intercalate ", " (f.params.map paramStr)
  let header := s!"{typeStr f.retType} {sanitizeIdent f.name}({paramsStr}) " ++ "{"
  let bodyLines := stmtLines 1 f.body
  let footer := "}"
  String.intercalate "\n" ([header] ++ bodyLines ++ [footer])

/-- Emit a `CProgramDecl` as a complete C source file with includes. -/
def programDecl (p : CProgramDecl) (includeHeader : Bool := true) : String :=
  let header := if includeHeader then
    "#include <stdlib.h>\n#include <stdint.h>\n"
  else ""
  let defs := p.defs.map funDecl
  let mainDef := funDecl p.main
  let allDefs := defs ++ [mainDef]
  header ++ String.intercalate "\n\n" allDefs ++ "\n"

end HeytingLean.LeanCP.CEmit
