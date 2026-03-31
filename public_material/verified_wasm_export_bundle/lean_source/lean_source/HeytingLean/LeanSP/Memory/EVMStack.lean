import HeytingLean.LeanSP.Arith.Word256

/-!
# LeanSP.Memory.EVMStack

EVM value stack model (max depth 1024).
Minimal — Yul abstracts the stack via named variables; this is mainly
for completeness and for modeling the few opcodes that interact with the
stack directly (DUP, SWAP — not used in Yul).
-/

namespace LeanSP.Memory

open LeanSP.Arith

/-- EVM value stack: array of Word256, max depth 1024. -/
structure EVMStack where
  data : Array Word256
  deriving Inhabited

def EVMStack.empty : EVMStack := ⟨#[]⟩
def EVMStack.maxDepth : Nat := 1024

def EVMStack.push (stack : EVMStack) (val : Word256) : Option EVMStack :=
  if stack.data.size ≥ EVMStack.maxDepth then none
  else some ⟨stack.data.push val⟩

def EVMStack.pop (stack : EVMStack) : Option (Word256 × EVMStack) :=
  if stack.data.isEmpty then none
  else some (stack.data.back!, ⟨stack.data.pop⟩)

def EVMStack.peek (stack : EVMStack) : Option Word256 :=
  stack.data.back?

def EVMStack.depth (stack : EVMStack) : Nat := stack.data.size

end LeanSP.Memory
