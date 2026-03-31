import HeytingLean.C.Syntax

/-!
# Emit tiny-C AST as C source code (Phase 4 utility)

This is a lightweight pretty-printer for the tiny `HeytingLean.C` fragment:
- integer expressions (plus comparisons encoded as `0/1`),
- assignments, sequencing, `if`, and `while`,
- functions returning a single integer (`long long`).

This is used by Phase 4 ("Quantum on a Laptop") to emit a repo-local `.c` file that can be compiled
and executed with the system toolchain, exercising the C back-end in a way the Lean type-checker
cannot.
-/

namespace HeytingLean
namespace C

open HeytingLean.C

namespace Emit

private def indent (n : Nat) : String :=
  String.intercalate "" (List.replicate (2 * n) " ")

private def paren (s : String) : String := s!"({s})"

private def sanitizeIdent (s : String) : String :=
  s.map (fun c => if c.isAlphanum || c = '_' then c else '_')

/-- Emit a `CExpr` as a C expression string (always parenthesized for safety). -/
def expr (e : CExpr) : String :=
  match e with
  | .intLit n => toString n
  | .var x => sanitizeIdent x
  | .arrayLength name => sanitizeIdent name ++ "_len"
  | .arrayIndex name idx => paren s!"{sanitizeIdent name}[{expr idx}]"
  | .add e₁ e₂ => paren s!"{expr e₁} + {expr e₂}"
  | .sub e₁ e₂ => paren s!"{expr e₁} - {expr e₂}"
  | .mul e₁ e₂ => paren s!"{expr e₁} * {expr e₂}"
  | .eq e₁ e₂  => paren s!"({expr e₁} == {expr e₂} ? 1 : 0)"
  | .le e₁ e₂  => paren s!"({expr e₁} <= {expr e₂} ? 1 : 0)"

/-! ### Constant folding on the tiny C AST. -/

private def foldExpr : CExpr → CExpr
  | .intLit n => .intLit n
  | .var x => .var x
  | .arrayLength name => .arrayLength name
  | .arrayIndex name idx => .arrayIndex name (foldExpr idx)
  | .add e₁ e₂ =>
      let e₁' := foldExpr e₁; let e₂' := foldExpr e₂
      match e₁', e₂' with
      | .intLit 0, e => e
      | e, .intLit 0 => e
      | .intLit n₁, .intLit n₂ => .intLit (n₁ + n₂)
      | _, _ => .add e₁' e₂'
  | .sub e₁ e₂ =>
      let e₁' := foldExpr e₁; let e₂' := foldExpr e₂
      match e₁', e₂' with
      | e, .intLit 0 => e
      | .intLit n₁, .intLit n₂ => .intLit (n₁ - n₂)
      | _, _ => .sub e₁' e₂'
  | .mul e₁ e₂ =>
      let e₁' := foldExpr e₁; let e₂' := foldExpr e₂
      match e₁', e₂' with
      | .intLit 0, _ => .intLit 0
      | _, .intLit 0 => .intLit 0
      | .intLit 1, e => e
      | e, .intLit 1 => e
      | .intLit n₁, .intLit n₂ => .intLit (n₁ * n₂)
      | _, _ => .mul e₁' e₂'
  | .eq e₁ e₂ =>
      let e₁' := foldExpr e₁; let e₂' := foldExpr e₂
      match e₁', e₂' with
      | .intLit n₁, .intLit n₂ => .intLit (if n₁ = n₂ then 1 else 0)
      | _, _ => .eq e₁' e₂'
  | .le e₁ e₂ =>
      let e₁' := foldExpr e₁; let e₂' := foldExpr e₂
      match e₁', e₂' with
      | .intLit n₁, .intLit n₂ => .intLit (if n₁ ≤ n₂ then 1 else 0)
      | _, _ => .le e₁' e₂'

private def foldStmt : CStmt → CStmt
  | .return e => .return (foldExpr e)
  | .assign x e => .assign x (foldExpr e)
  | .arrayUpdate name idx e => .arrayUpdate name (foldExpr idx) (foldExpr e)
  | .seq s₁ s₂ => .seq (foldStmt s₁) (foldStmt s₂)
  | .if_ c t e => .if_ (foldExpr c) (foldStmt t) (foldStmt e)
  | .while c b => .while (foldExpr c) (foldStmt b)

private def usedVarsExpr : CExpr → List Ident
  | .intLit _ => []
  | .var x => [x]
  | .arrayLength name => [name]
  | .arrayIndex name idx => name :: usedVarsExpr idx
  | .add e₁ e₂ => usedVarsExpr e₁ ++ usedVarsExpr e₂
  | .sub e₁ e₂ => usedVarsExpr e₁ ++ usedVarsExpr e₂
  | .mul e₁ e₂ => usedVarsExpr e₁ ++ usedVarsExpr e₂
  | .eq e₁ e₂ => usedVarsExpr e₁ ++ usedVarsExpr e₂
  | .le e₁ e₂ => usedVarsExpr e₁ ++ usedVarsExpr e₂

private def arrayNamesExpr : CExpr → List Ident
  | .intLit _ => []
  | .var _ => []
  | .arrayLength name => [name]
  | .arrayIndex name idx => name :: arrayNamesExpr idx
  | .add e₁ e₂ => arrayNamesExpr e₁ ++ arrayNamesExpr e₂
  | .sub e₁ e₂ => arrayNamesExpr e₁ ++ arrayNamesExpr e₂
  | .mul e₁ e₂ => arrayNamesExpr e₁ ++ arrayNamesExpr e₂
  | .eq e₁ e₂ => arrayNamesExpr e₁ ++ arrayNamesExpr e₂
  | .le e₁ e₂ => arrayNamesExpr e₁ ++ arrayNamesExpr e₂

private def usedVarsStmt : CStmt → List Ident
  | .return e => usedVarsExpr e
  | .assign x e => x :: usedVarsExpr e
  | .arrayUpdate name idx e => name :: (usedVarsExpr idx ++ usedVarsExpr e)
  | .seq s₁ s₂ => usedVarsStmt s₁ ++ usedVarsStmt s₂
  | .if_ cond t e => usedVarsExpr cond ++ usedVarsStmt t ++ usedVarsStmt e
  | .while cond b => usedVarsExpr cond ++ usedVarsStmt b

private def arrayNamesStmt : CStmt → List Ident
  | .return e => arrayNamesExpr e
  | .assign _ e => arrayNamesExpr e
  | .arrayUpdate name idx e => name :: (arrayNamesExpr idx ++ arrayNamesExpr e)
  | .seq s₁ s₂ => arrayNamesStmt s₁ ++ arrayNamesStmt s₂
  | .if_ cond t e => arrayNamesExpr cond ++ arrayNamesStmt t ++ arrayNamesStmt e
  | .while cond b => arrayNamesExpr cond ++ arrayNamesStmt b

private def assignedVars : CStmt → List Ident
  | .return _ => []
  | .assign x _ => [x]
  | .arrayUpdate _ _ _ => []
  | .seq s₁ s₂ => assignedVars s₁ ++ assignedVars s₂
  | .if_ _ t e => assignedVars t ++ assignedVars e
  | .while _ b => assignedVars b

private def locals (params : List Ident) (body : CStmt) : List Ident :=
  (assignedVars body).eraseDups.filter (fun x => !(params.contains x))

private def stmtLines : Nat → CStmt → List String
  | n, .return e => [s!"{indent n}return {expr e};"]
  | n, .assign x e => [s!"{indent n}{sanitizeIdent x} = {expr e};"]
  | n, .arrayUpdate name idx e =>
      [s!"{indent n}{sanitizeIdent name}[{expr idx}] = {expr e};"]
  | n, .seq s₁ s₂ => stmtLines n s₁ ++ stmtLines n s₂
  | n, .if_ cond t e =>
      let head := indent n ++ "if (" ++ expr cond ++ " != 0) {"
      let mid := indent n ++ "} else {"
      let tail := indent n ++ "}"
      [head] ++ stmtLines (n+1) t ++ [mid] ++ stmtLines (n+1) e ++ [tail]
  | n, .while cond body =>
      let head := indent n ++ "while (" ++ expr cond ++ " != 0) {"
      let tail := indent n ++ "}"
      [head] ++ stmtLines (n+1) body ++ [tail]

private def cType : String := "long long"

private def paramDecl (arrayNames : List Ident) (p : Ident) : String :=
  let p' := sanitizeIdent p
  if arrayNames.contains p then
    s!"{cType}* {p'}"
  else
    s!"{cType} {p'}"

private def paramsDecl (arrayNames : List Ident) (ps : List Ident) : String :=
  String.intercalate ", " (ps.map (paramDecl arrayNames))

/-- Emit a `CFun` to a C function definition string. -/
def funDef (f : CFun) : String :=
  let body := foldStmt f.body
  let arrayNs := (arrayNamesStmt body).eraseDups
  let arrayLocals := arrayNs.filter (fun name => !(f.params.contains name))
  let ls := locals f.params body
  let arrayDecls := arrayLocals.map (fun name => s!"{indent 1}{cType} {sanitizeIdent name}[16] = {0};")
  let lenDecls := arrayNs.map (fun name => s!"{indent 1}{cType} {sanitizeIdent name}_len = 16;")
  let decls := ls.map (fun x => s!"{indent 1}{cType} {sanitizeIdent x} = 0;")
  let used := (usedVarsStmt body).eraseDups
  let unused := f.params.filter (fun p => !(used.contains p))
  let paramSilence := unused.map (fun p => s!"{indent 1}(void){paren (sanitizeIdent p)};")
  let header := s!"{cType} {sanitizeIdent f.name}({paramsDecl arrayNs f.params}) " ++ "{"
  let footer := "}"
  String.intercalate "\n" ([header] ++ paramSilence ++ arrayDecls ++ lenDecls ++ decls ++ stmtLines 1 body ++ [footer])

/-- Emit multiple `CFun` definitions, separated by blank lines. -/
def funDefs (fs : List CFun) : String :=
  String.intercalate "\n\n" (fs.map funDef)

end Emit

end C
end HeytingLean
