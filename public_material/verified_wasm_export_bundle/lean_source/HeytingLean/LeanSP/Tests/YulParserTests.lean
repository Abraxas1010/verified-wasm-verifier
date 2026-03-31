import HeytingLean.LeanSP.Pipeline.ContractLoader

/-!
# LeanSP.Tests.YulParserTests

Parser tests for Phase 1 gate.
-/

namespace LeanSP.Tests

open LeanSP.Pipeline
open HeytingLean.BountyHunter.Solc

-- Test 1: Parse minimal Yul statements
#eval do
  let src := "let x := add(1, 2)"
  match YulTextMini.parseStmtsFromStringE src with
  | .ok stmts => return s!"Test 1 PASS: parsed {stmts.size} stmts"
  | .error e => return s!"Test 1 FAIL: {e}"

-- Test 2: List function names
#eval do
  let src := "function foo() { let x := 1 } function bar() { let y := 2 }"
  match YulTextMini.listFunctionNamesE src with
  | .ok names => return s!"Test 2 PASS: found functions {names.toList}"
  | .error e => return s!"Test 2 FAIL: {e}"

-- Test 3: Parse function body
#eval do
  let src := "function foo() { let x := add(1, 2) }"
  match YulTextMini.parseFunctionBodyE src "foo" with
  | .ok stmts => return s!"Test 3 PASS: foo has {stmts.size} stmts"
  | .error e => return s!"Test 3 FAIL: {e}"

-- Test 4: Extract full FuncDef
#eval do
  let src := "function checked_add(x, y) { let sum := add(x, y) }"
  match extractFuncDefs src with
  | .ok funcs =>
      if funcs.isEmpty then return "Test 4 FAIL: no funcs extracted"
      else
        let f := funcs[0]!
        return s!"Test 4 PASS: {f.name} params={f.params.toList} body={f.body.size} stmts"
  | .error e => return s!"Test 4 FAIL: {e}"

-- Test 5: Parse Yul object structure
#eval do
  let src := "object \"Test\" { code { let x := 42 } }"
  match parseYulText src with
  | .ok unit =>
      return s!"Test 5 PASS: object={unit.objectName}, funcs={unit.functions.size}, top={unit.topLevelStmts.size}"
  | .error e => return s!"Test 5 FAIL: {e}"

-- Test 6: Function with params and returns
#eval do
  let src := "function add_safe(a, b) -> result { result := add(a, b) }"
  match extractFuncDefs src with
  | .ok funcs =>
      if funcs.isEmpty then return "Test 6 FAIL: no funcs"
      else
        let f := funcs[0]!
        return s!"Test 6 PASS: {f.name} params={f.params.toList} returns={f.returns.toList}"
  | .error e => return s!"Test 6 FAIL: {e}"

end LeanSP.Tests
