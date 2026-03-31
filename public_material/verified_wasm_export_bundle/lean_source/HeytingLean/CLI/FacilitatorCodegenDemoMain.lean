import HeytingLean.Blockchain.Facilitator.Extraction.MiniC
import HeytingLean.C.Emit

/-!
# `facilitator_codegen_demo` (Phase 3)

Repo-local hook that emits a tiny C file for the “trustless facilitator” kernel
using the verified MiniC→tiny-C compiler path.

This executable:
- computes an `expected.txt` via the MiniC fragment semantics, and
- emits `generated.c` containing the compiled functions + a small driver `main()`.

It does **not** invoke an external C compiler; use `scripts/build_facilitator_local.sh`.
-/

namespace HeytingLean
namespace CLI
namespace FacilitatorCodegenDemo

open HeytingLean
open HeytingLean.C
open HeytingLean.C.Emit
open HeytingLean.Blockchain.Facilitator
open HeytingLean.Blockchain.Facilitator.Extraction

structure Config where
  outDir : String := "dist/facilitator_codegen_demo"
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "facilitator_codegen_demo (Phase 3)"
    , ""
    , "Emits:"
    , "  - generated.c        (C source for facilitator functions + a tiny driver main)"
    , "  - expected.txt       (expected stdout from driver main)"
    , "  - minic.repr.txt     (debug repr of the MiniC functions)"
    , ""
    , "Flags:"
    , "  --out <dir>    output directory (relative to repo root unless absolute)"
    , "  --help         show this message"
    ]

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) :=
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--out" :: dir :: rest => parseArgs rest { cfg with outDir := dir }
  | x :: _ => throw <| IO.userError s!"unknown arg: {x} (try --help)"

private def resolveOutDir (dir : String) : IO System.FilePath := do
  if dir.startsWith "/" then
    return System.FilePath.mk dir

  let cwd ← IO.currentDir
  let base :=
    if cwd.fileName == some "lean" then
      cwd.parent.getD cwd
    else
      cwd
  return base / dir

private def writeFile (path : System.FilePath) (contents : String) : IO Unit := do
  let some parent := path.parent
    | throw <| IO.userError s!"could not compute parent directory for {path}"
  IO.FS.createDirAll parent
  IO.FS.writeFile path contents

private def driverMainSource
    (sender recipient amount nonce senderBal recipientBal senderNonce sigOk : Int) : String :=
  String.intercalate "\n"
    [ "int main(void) {"
    , s!"  long long sender = {sender};"
    , s!"  long long recipient = {recipient};"
    , s!"  long long amount = {amount};"
    , s!"  long long nonce = {nonce};"
    , s!"  long long senderBal = {senderBal};"
    , s!"  long long recipientBal = {recipientBal};"
    , s!"  long long senderNonce = {senderNonce};"
    , s!"  long long sigOk = {sigOk};"
    , "  printf(\"%lld\\n\", facilitator_verify(sender, recipient, amount, nonce, senderBal, senderNonce, sigOk));"
    , "  printf(\"%lld\\n\", facilitator_settle_senderBal_if_valid(sender, recipient, amount, nonce, senderBal, senderNonce, sigOk));"
    , "  printf(\"%lld\\n\", facilitator_settle_recipientBal_if_valid(sender, recipient, amount, nonce, recipientBal, senderBal, senderNonce, sigOk));"
    , "  printf(\"%lld\\n\", facilitator_settle_senderNonce_if_valid(sender, recipient, amount, nonce, senderNonce, senderBal, sigOk));"
    , "  return 0;"
    , "}"
    ]

def main (argv : List String) : IO UInt32 := do
  try
    let (cfg, showHelp) ← parseArgs argv
    if showHelp then
      IO.println usage
      return (0 : UInt32)

    let outDir ← resolveOutDir cfg.outDir

    -- Demo inputs (chosen to satisfy the validity predicate).
    let sender : Nat := 1
    let recipient : Nat := 2
    let amount : Nat := 12
    let nonce : Nat := 7
    let senderBal : Nat := 20
    let recipientBal : Nat := 3
    let senderNonce : Nat := 7
    let sigOk : Nat := 1

    let some outVerify :=
      Extraction.FragRunner.runNatFunFragN MiniCImpl.verifyFun
        [sender, recipient, amount, nonce, senderBal, senderNonce, sigOk]
      | throw <| IO.userError "failed to run facilitator_verify under MiniC fragment semantics"
    let some outSenderBal :=
      Extraction.FragRunner.runNatFunFragN MiniCImpl.settleSenderBalIfValidFun
        [sender, recipient, amount, nonce, senderBal, senderNonce, sigOk]
      | throw <| IO.userError "failed to run facilitator_settle_senderBal_if_valid under MiniC fragment semantics"
    let some outRecipientBal :=
      Extraction.FragRunner.runNatFunFragN MiniCImpl.settleRecipientBalIfValidFun
        [sender, recipient, amount, nonce, recipientBal, senderBal, senderNonce, sigOk]
      | throw <| IO.userError "failed to run facilitator_settle_recipientBal_if_valid under MiniC fragment semantics"
    let some outSenderNonce :=
      Extraction.FragRunner.runNatFunFragN MiniCImpl.settleSenderNonceIfValidFun
        [sender, recipient, amount, nonce, senderNonce, senderBal, sigOk]
      | throw <| IO.userError "failed to run facilitator_settle_senderNonce_if_valid under MiniC fragment semantics"

    let cPath := outDir / "generated.c"
    let expectedPath := outDir / "expected.txt"
    let minicPath := outDir / "minic.repr.txt"

    let cHeader :=
      String.intercalate "\n"
        [ "/* Generated by HeytingLean (facilitator_codegen_demo) — Phase 3"
        , "   Trustless facilitator kernel (verification + settlement arithmetic)."
        , "*/"
        , "#include <stdio.h>"
        , ""
        ]
    let cDefs :=
      Emit.funDefs
        [ MiniC.ToC.compileFun MiniCImpl.verifyFun
        , MiniC.ToC.compileFun MiniCImpl.settleSenderBalIfValidFun
        , MiniC.ToC.compileFun MiniCImpl.settleRecipientBalIfValidFun
        , MiniC.ToC.compileFun MiniCImpl.settleSenderNonceIfValidFun
        ]
    let driver :=
      driverMainSource
        (sender := Int.ofNat sender)
        (recipient := Int.ofNat recipient)
        (amount := Int.ofNat amount)
        (nonce := Int.ofNat nonce)
        (senderBal := Int.ofNat senderBal)
        (recipientBal := Int.ofNat recipientBal)
        (senderNonce := Int.ofNat senderNonce)
        (sigOk := Int.ofNat sigOk)
    let cSource := cHeader ++ cDefs ++ "\n\n" ++ driver ++ "\n"

    writeFile cPath cSource
    writeFile expectedPath
      (toString outVerify ++ "\n" ++ toString outSenderBal ++ "\n" ++
        toString outRecipientBal ++ "\n" ++ toString outSenderNonce ++ "\n")
    writeFile minicPath
      (reprStr MiniCImpl.verifyFun ++ "\n\n" ++
        reprStr MiniCImpl.settleSenderBalIfValidFun ++ "\n\n" ++
        reprStr MiniCImpl.settleRecipientBalIfValidFun ++ "\n\n" ++
        reprStr MiniCImpl.settleSenderNonceIfValidFun ++ "\n")

    IO.println s!"[facilitator_codegen_demo] wrote {cPath}"
    IO.println s!"[facilitator_codegen_demo] wrote {expectedPath} (expected stdout)"
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"[facilitator_codegen_demo] error: {e}"
    return (1 : UInt32)

end FacilitatorCodegenDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.FacilitatorCodegenDemo.main args
