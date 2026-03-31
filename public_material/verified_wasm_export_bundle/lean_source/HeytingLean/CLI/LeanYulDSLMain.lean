import Std
import HeytingLean.CLI.Args
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Examples

/-!
# HeytingLean.CLI.LeanYulDSLMain

Emit Lean-generated example contracts as canonical Yul object source.

This is a tiny, deterministic CLI intended to support external compilation
(e.g. `solc --standard-json`) and downstream smoke tests.
-/

open HeytingLean.Blockchain.Contracts.LeanYulDSL

private def usage : String :=
  String.intercalate "\n"
    [
      "Usage:",
      "  lean_yul_dsl_cli --example owner|bank|erc20 [--out PATH]",
      "",
      "Examples:",
      "  lean_yul_dsl_cli --example owner",
      "  lean_yul_dsl_cli --example bank --out /tmp/bank.yul",
      "  lean_yul_dsl_cli --example erc20 --out /tmp/erc20.yul",
    ]

private def getArgValue? (flag : String) (args : List String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | a :: b :: rest => if a = flag then some b else go (b :: rest)
    | [_] => none
  go args

private def hasFlag (flag : String) (args : List String) : Bool :=
  args.any (fun a => a = flag)

def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  if args.isEmpty || hasFlag "--help" args || hasFlag "-h" args then
    IO.println usage
    return 0
  let ex? := getArgValue? "--example" args
  let out? := getArgValue? "--out" args
  match ex? with
  | none =>
      IO.eprintln usage
      pure 1
  | some slug =>
      match exampleBySlug? slug with
      | none =>
          IO.eprintln s!"unknown --example {slug}\n\n{usage}"
          pure 1
      | some (_id, prog) =>
          let yul := exampleToYul prog
          match out? with
          | none =>
              IO.print yul
              pure 0
          | some path =>
              IO.FS.writeFile path yul
              pure 0
