import Lean

/-!
Minimal EVM opcode AST and pretty-printer. This is a foundation for
generating on-chain bytecode from Lean later in the pipeline.
-/

namespace HeytingLean
namespace Compiler
namespace EVM

inductive Opcode where
  | PUSH (n : Nat) (value : ByteArray)  -- PUSH1..PUSH32
  | DUP (n : Nat)
  | SWAP (n : Nat)
  | ADD | MUL | SUB | DIV | MOD
  | EQ | ISZERO | AND | OR | XOR | NOT
  | MLOAD | MSTORE | CALLDATALOAD
  | JUMP | JUMPI | JUMPDEST
  | RETURN | REVERT | STOP

open Opcode

def opcodeName : Opcode → String
  | PUSH n _ => s!"PUSH{n}"
  | DUP n => s!"DUP{n}"
  | SWAP n => s!"SWAP{n}"
  | ADD => "ADD" | MUL => "MUL" | SUB => "SUB" | DIV => "DIV" | MOD => "MOD"
  | EQ => "EQ" | ISZERO => "ISZERO" | AND => "AND" | OR => "OR" | XOR => "XOR" | NOT => "NOT"
  | MLOAD => "MLOAD" | MSTORE => "MSTORE" | CALLDATALOAD => "CALLDATALOAD"
  | JUMP => "JUMP" | JUMPI => "JUMPI" | JUMPDEST => "JUMPDEST"
  | RETURN => "RETURN" | REVERT => "REVERT" | STOP => "STOP"

def showOpcode (op : Opcode) : String :=
  match op with
  | PUSH _ v =>
      let hexDigit (d : Nat) : Char :=
        if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + (d - 10))
      let toHexPair (b : UInt8) : String :=
        let n := b.toNat
        let hi := hexDigit ((n / 16) % 16)
        let lo := hexDigit (n % 16)
        String.mk [hi, lo]
      let s := Id.run do
        let mut acc := ""
        for i in [:v.size] do
          acc := acc ++ toHexPair (v.get! i)
        return acc
      opcodeName op ++ " 0x" ++ s
  | _ => opcodeName op

def pretty (ops : List Opcode) : String := String.intercalate "\n" (ops.map showOpcode)

end EVM
end Compiler
end HeytingLean
