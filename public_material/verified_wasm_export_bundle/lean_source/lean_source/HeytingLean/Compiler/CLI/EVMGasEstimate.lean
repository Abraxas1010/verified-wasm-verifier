import Lean
import HeytingLean.Compiler.ToEVM

/-!
Simple gas estimator CLI for a minimal verifier opcode list.
Includes a base verify cost to approximate BN254 precompile usage.
-/

namespace HeytingLean
namespace Compiler
namespace CLI

open EVM

def estimateGas (ops : List Opcode) : Nat :=
  let base := 180000 -- approximate pairing precompile baseline
  ops.foldl (fun acc op =>
    acc + match op with
    | .ADD | .SUB => 3
    | .MUL | .DIV | .MOD => 5
    | .MLOAD | .MSTORE => 3
    | .CALLDATALOAD => 3
    | .PUSH _ _ => 3
    | .DUP _ => 3
    | .SWAP _ => 3
    | .JUMPI => 10
    | .JUMP => 8
    | .EQ | .ISZERO | .AND | .OR | .XOR | .NOT => 3
    | .JUMPDEST => 1
    | .RETURN | .REVERT | .STOP => 0
  ) base

def minimalVerifierOpcodes : List Opcode :=
  let w := ByteArray.mk #[0,0,0,0]
  [
    Opcode.CALLDATALOAD,
    Opcode.PUSH 32 w,
    Opcode.DUP 1,
    Opcode.ADD,
    Opcode.MUL,
    Opcode.JUMPI,
    Opcode.JUMPDEST,
    Opcode.MLOAD,
    Opcode.MSTORE,
    Opcode.RETURN
  ]

def main (_args : List String) : IO UInt32 := do
  -- Usage: lake exe evm_gas_estimate [--verifier minimal_verifier.evm]
  let ops := minimalVerifierOpcodes
  let gas := estimateGas ops
  IO.println s!"gas_estimate: {gas}"
  return 0

end CLI
end Compiler
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.Compiler.CLI.main args
