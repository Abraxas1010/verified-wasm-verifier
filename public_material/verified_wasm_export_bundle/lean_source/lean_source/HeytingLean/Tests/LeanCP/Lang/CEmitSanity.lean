import HeytingLean.LeanCP.Lang.CEmit
import HeytingLean.LeanCP.Compile.SKYLowering

/-!
# CEmit Sanity Tests

Verify that `CEmit` produces non-empty, deterministic output for the
SKY reducer program and exercises each major AST constructor path.
-/

namespace HeytingLean.Tests.LeanCP.Lang.CEmitSanity

open HeytingLean.LeanCP
open HeytingLean.LeanCP.CEmit
open HeytingLean.LeanCP.Compile.SKYLowering

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

-- The emitted program is non-empty
#guard (programDecl skyReducerProgram).length > 100

-- The emitted program contains the function name
#guard hasSubstr (programDecl skyReducerProgram) "sky_reducer_step"

-- The emitted program contains the return type
#guard hasSubstr (programDecl skyReducerProgram) "int "

-- The emitted program contains parameter names
#guard hasSubstr (programDecl skyReducerProgram) "tags"
#guard hasSubstr (programDecl skyReducerProgram) "lhs"
#guard hasSubstr (programDecl skyReducerProgram) "rhs"
#guard hasSubstr (programDecl skyReducerProgram) "oracleRefs"
#guard hasSubstr (programDecl skyReducerProgram) "focusPtr"
#guard hasSubstr (programDecl skyReducerProgram) "maxNodes"

-- The emitted program contains expected C constructs
#guard hasSubstr (programDecl skyReducerProgram) "if ("
#guard hasSubstr (programDecl skyReducerProgram) "return "
#guard hasSubstr (programDecl skyReducerProgram) "#include"

-- Determinism: two calls produce the same output
#guard (programDecl skyReducerProgram) == (programDecl skyReducerProgram)

-- Exercise type rendering
#guard typeStr .int == "int"
#guard typeStr .void == "void"
#guard typeStr (.ptr .int) == "int*"
#guard typeStr (.intSized .Signed .I32) == "int32_t"
#guard typeStr (.intSized .Unsigned .I16) == "uint16_t"
#guard typeStr (.intSized .Signed .I64) == "int64_t"
#guard typeStr (.intSized .Unsigned .I64) == "uint64_t"
#guard typeStr (.struct "node") == "struct node"

-- Exercise operator rendering
#guard binOpStr .add == "+"
#guard binOpStr .eq == "=="
#guard binOpStr .bitAnd == "&"
#guard binOpStr .shl == "<<"

-- Exercise expression rendering
#guard exprStr (.intLit 42) == "42"
#guard exprStr .null == "NULL"
#guard exprStr (.var "x") == "x"
#guard hasSubstr (exprStr (.binop .add (.var "a") (.intLit 1))) "a + 1"

-- Exercise simple statement rendering
#guard (stmtLines 0 .skip).length == 0
#guard (stmtLines 0 (.ret (.intLit 0))).length == 1
#guard hasSubstr (stmtLines 0 (.ret (.intLit 0))).head! "return 0"

-- Exercise funDecl on a minimal function
private def minFun : CFunDecl :=
  { name := "test_fn"
    params := [("a", .int), ("b", .int)]
    retType := .int
    body := .ret (.binop .add (.var "a") (.var "b")) }

#guard hasSubstr (funDecl minFun) "int test_fn(int a, int b)"
#guard hasSubstr (funDecl minFun) "return (a + b)"

-- Exercise programDecl without header
#guard !hasSubstr (programDecl skyReducerProgram (includeHeader := false)) "#include"

-- I64 support: bit width
#guard IntSize.I64.bits == 64

-- I64 support: modulus
#guard uintModulus .I64 == 18446744073709551616

-- I64 support: promotion (I64 dominates all)
#guard promoteUIntSize .I64 .I8 == .I64
#guard promoteUIntSize .I32 .I64 == .I64
#guard promoteUIntSize .I64 .I64 == .I64

-- I64 support: wrapping arithmetic
#guard wrapUnsignedInt .I64 255 == 255
#guard wrapSignedInt .I64 (-1) == -1

-- Float support: type rendering
#guard typeStr .float == "float"
#guard typeStr .double == "double"

-- Float support: expression rendering
#guard exprStr (.floatLit 3.14) == "3.140000"

-- Float support: truthiness
#guard isTruthy (.float 1.0) == true
#guard isTruthy (.float 0.0) == false

end HeytingLean.Tests.LeanCP.Lang.CEmitSanity
