import HeytingLean.LeanCP.Lang.RustSyntax

/-!
# LeanCP Rust Emission

Pure pretty-printer for the Rust IR to concrete `.rs` source text.
Follows the same conventions as `CEmit.lean`:
- 4-space indentation (Rust convention)
- identifiers sanitized to [A-Za-z0-9_]
- deterministic output (no IO, no randomness)
-/

namespace HeytingLean.LeanCP.Rust.Emit

open HeytingLean.LeanCP
open HeytingLean.LeanCP.Rust

private def indent (n : Nat) : String :=
  String.intercalate "" (List.replicate (4 * n) " ")

private def paren (s : String) : String := "(" ++ s ++ ")"

private def rustKeywords : List String :=
  ["as", "break", "const", "continue", "crate", "else", "enum", "extern",
   "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod",
   "move", "mut", "pub", "ref", "return", "self", "Self", "static", "struct",
   "super", "trait", "true", "type", "unsafe", "use", "where", "while",
   "async", "await", "dyn", "abstract", "become", "box", "do", "final",
   "macro", "override", "priv", "typeof", "unsized", "virtual", "yield"]

private def sanitizeIdent (s : String) : String :=
  let s' := s.map (fun c => if c.isAlphanum || c = '_' then c else '_')
  let s'' := if s'.isEmpty then "_empty" else s'
  if rustKeywords.contains s'' then "r_" ++ s'' else s''

/-- Render a RustType as a Rust type string. -/
partial def typeStr : RustType → String
  | .i8  => "i8"
  | .i16 => "i16"
  | .i32 => "i32"
  | .i64 => "i64"
  | .u8  => "u8"
  | .u16 => "u16"
  | .u32 => "u32"
  | .u64 => "u64"
  | .f32 => "f32"
  | .f64 => "f64"
  | .bool => "bool"
  | .unit => "()"
  | .rawPtr inner true  => "*mut " ++ typeStr inner
  | .rawPtr inner false => "*const " ++ typeStr inner
  | .slice inner => "&[" ++ typeStr inner ++ "]"
  | .array inner n => "[" ++ typeStr inner ++ "; " ++ toString n ++ "]"
  | .namedStruct name => sanitizeIdent name
  | .namedEnum name => sanitizeIdent name
  | .usize => "usize"

/-- Render a BinOp as its Rust operator token. -/
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

/-- Render a RustExpr as a Rust expression string. -/
partial def exprStr : RustExpr → String
  | .var x            => sanitizeIdent x
  | .intLit n         => toString n
  | .floatLit v       => toString v
  | .boolLit true     => "true"
  | .boolLit false    => "false"
  | .nullPtr ty       => "std::ptr::null_mut::<" ++ typeStr ty ++ ">()"
  | .sizeOf ty        => "std::mem::size_of::<" ++ typeStr ty ++ ">()"
  | .cast ty e        => paren (exprStr e ++ " as " ++ typeStr ty)
  | .binop op e1 e2   => paren (exprStr e1 ++ " " ++ binOpStr op ++ " " ++ exprStr e2)
  | .unsafeDeref e    => "*" ++ exprStr e
  | .arrayAccess a i  =>
      "*" ++ exprStr a ++ ".add(" ++ exprStr i ++ " as usize)"
  | .addrOf x true    => "&mut " ++ sanitizeIdent x
  | .addrOf x false   => "&" ++ sanitizeIdent x
  | .fieldAccess e f  =>
      "(*" ++ exprStr e ++ ")." ++ sanitizeIdent f
  | .call fn args     =>
      let argStrs := args.map exprStr
      sanitizeIdent fn ++ "(" ++ String.intercalate ", " argStrs ++ ")"

/-- Check if a RustExpr is already a boolean-typed expression (comparison). -/
def isBoolExpr : RustExpr → Bool
  | .binop .eq _ _  => true
  | .binop .ne _ _  => true
  | .binop .lt _ _  => true
  | .binop .le _ _  => true
  | .binop .gt _ _  => true
  | .binop .ge _ _  => true
  | .binop .and _ _ => true
  | .binop .or _ _  => true
  | .binop .lAnd _ _ => true
  | .binop .lOr _ _  => true
  | .boolLit _      => true
  | _                => false

/-- Emit a condition expression. If already boolean, emit directly; otherwise add `!= 0`. -/
def condStr (e : RustExpr) : String :=
  if isBoolExpr e then exprStr e
  else exprStr e ++ " != 0"

/-- Render a RustStmt as a list of indented Rust source lines. -/
partial def stmtLines (n : Nat) : RustStmt → List String
  | .skip => []
  | .letBind x ty e isMut =>
      let mutStr := if isMut then "mut " else ""
      [indent n ++ "let " ++ mutStr ++ sanitizeIdent x ++ ": " ++ typeStr ty ++ " = " ++ exprStr e ++ ";"]
  | .assign lhs rhs =>
      [indent n ++ exprStr lhs ++ " = " ++ exprStr rhs ++ ";"]
  | .seq s1 s2 =>
      stmtLines n s1 ++ stmtLines n s2
  | .ite cond th el =>
      let hd := indent n ++ "if " ++ condStr cond ++ " {"
      let mid := indent n ++ "} else {"
      let tl := indent n ++ "}"
      [hd] ++ stmtLines (n + 1) th ++ [mid] ++ stmtLines (n + 1) el ++ [tl]
  | .whileLoop cond body =>
      let hd := indent n ++ "while " ++ condStr cond ++ " {"
      let tl := indent n ++ "}"
      [hd] ++ stmtLines (n + 1) body ++ [tl]
  | .forRange var_ lo hi body =>
      let hd := indent n ++ "for " ++ sanitizeIdent var_ ++ " in (" ++ exprStr lo ++ ")..(" ++ exprStr hi ++ ") {"
      let tl := indent n ++ "}"
      [hd] ++ stmtLines (n + 1) body ++ [tl]
  | .block body =>
      let hd := indent n ++ "{"
      let tl := indent n ++ "}"
      [hd] ++ stmtLines (n + 1) body ++ [tl]
  | .unsafeBlock body =>
      let hd := indent n ++ "unsafe {"
      let tl := indent n ++ "}"
      [hd] ++ stmtLines (n + 1) body ++ [tl]
  | .ret e =>
      [indent n ++ "return " ++ exprStr e ++ ";"]
  | .alloc x cells ty =>
      [indent n ++ "let " ++ sanitizeIdent x ++ ": *mut " ++ typeStr ty
        ++ " = std::alloc::alloc(std::alloc::Layout::array::<" ++ typeStr ty
        ++ ">(" ++ toString cells ++ ").unwrap()) as *mut " ++ typeStr ty ++ ";"]
  | .free e ty cells =>
      [indent n ++ "std::alloc::dealloc(" ++ exprStr e ++ " as *mut u8, std::alloc::Layout::array::<"
        ++ typeStr ty ++ ">(" ++ toString cells ++ ").unwrap());"]
  | .break_ =>
      [indent n ++ "break;"]
  | .continue_ =>
      [indent n ++ "continue;"]

/-- Emit a parameter declaration. -/
def paramStr (p : String × RustType) : String :=
  sanitizeIdent p.1 ++ ": " ++ typeStr p.2

/-- Emit a RustFunDecl as a complete Rust function definition. -/
def funDecl (f : RustFunDecl) : String :=
  let paramsStr := String.intercalate ", " (f.params.map paramStr)
  let unsafeStr := if f.isUnsafe then "unsafe " else ""
  let retStr := match f.retType with
    | .unit => ""
    | ty => " -> " ++ typeStr ty
  let header := unsafeStr ++ "fn " ++ sanitizeIdent f.name ++ "(" ++ paramsStr ++ ")" ++ retStr ++ " {"
  let bodyLines := stmtLines 1 f.body
  let footer := "}"
  String.intercalate "\n" ([header] ++ bodyLines ++ [footer])

/-- Emit a RustProgramDecl as a complete Rust source file. -/
def programDecl (p : RustProgramDecl) : String :=
  let defs := p.defs.map funDecl
  let mainDef := funDecl p.main
  let allDefs := defs ++ [mainDef]
  String.intercalate "\n\n" allDefs ++ "\n"

end HeytingLean.LeanCP.Rust.Emit
