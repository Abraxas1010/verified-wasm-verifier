import Lean
-- VM module is self-contained in this file

open Lean
open System

/-- BoolLens VM bytecode instructions -/
inductive Instruction
  | PUSH (val : Bool)
  | POP
  | AND
  | OR
  | NOT
  | DUP
  | SWAP
  | RET
  | JMP (offset : Int)
  | JZ (offset : Int)  -- Jump if zero/false
  deriving Repr, DecidableEq

/-- VM State -/
structure VMState where
  stack : List Bool
  pc : Nat  -- Program counter
  gas : Nat
  trace : List (Nat × String × List Bool)
  deriving Repr

/-- Command-line VM executor -/
def main (args : List String) : IO Unit := do
  -- Check arguments
  if args.length != 1 then
    IO.eprintln "Usage: vm_execute <program_file.json>"
    IO.Process.exit 1

  let inputFile := args.head!

  -- Read input file
  let inputContent ← IO.FS.readFile inputFile

  -- Parse JSON input
  let inputJson : Json ← match Json.parse inputContent with
    | Except.ok json => pure json
    | Except.error e => do
      IO.eprintln s!"Failed to parse JSON: {e}"
      IO.Process.exit 1

  -- Extract bytecode and input
  let bytecodeJson := inputJson.getObjValAs? (Array Json) "bytecode" |>.getD #[]
  let bytecode ← parseBytecode bytecodeJson.toList

  -- Initialize VM state
  let initialState : VMState := {
    stack := []
    pc := 0
    gas := 1000
    trace := []
  }

  -- Execute program
  let finalState ← executeProgram bytecode initialState

  -- Create output JSON
  let resultJson := match finalState.stack.head? with
    | some b => Json.bool b
    | none => Json.null

  let traceJson := Json.arr (finalState.trace.map fun (pc, op, stack) =>
    Json.mkObj [
      ("pc", Json.num pc),
      ("op", Json.str op),
      ("stack", Json.arr (stack.map Json.bool))
    ])

  let output := Json.mkObj [
    ("ok", Json.bool true),
    ("result", resultJson),
    ("gasUsed", Json.num (1000 - finalState.gas)),
    ("finalStack", Json.arr (finalState.stack.map Json.bool)),
    ("trace", traceJson)
  ]

  -- Write output
  IO.println output.compress

where
  /-- Parse bytecode from JSON array -/
  parseBytecode (ops : List Json) : IO (List Instruction) := do
    let mut instructions := []
    let mut i := 0
    while i < ops.length do
      match ops.get? i with
      | some (Json.str op) =>
        match op with
        | "PUSH" =>
          -- Next element should be the value
          match ops.get? (i + 1) with
          | some (Json.bool b) =>
            instructions := instructions ++ [Instruction.PUSH b]
            i := i + 2
          | some (Json.str "true") =>
            instructions := instructions ++ [Instruction.PUSH true]
            i := i + 2
          | some (Json.str "false") =>
            instructions := instructions ++ [Instruction.PUSH false]
            i := i + 2
          | _ =>
            IO.eprintln s!"Invalid PUSH argument at position {i+1}"
            IO.Process.exit 1
        | "POP" =>
          instructions := instructions ++ [Instruction.POP]
          i := i + 1
        | "AND" =>
          instructions := instructions ++ [Instruction.AND]
          i := i + 1
        | "OR" =>
          instructions := instructions ++ [Instruction.OR]
          i := i + 1
        | "NOT" =>
          instructions := instructions ++ [Instruction.NOT]
          i := i + 1
        | "DUP" =>
          instructions := instructions ++ [Instruction.DUP]
          i := i + 1
        | "SWAP" =>
          instructions := instructions ++ [Instruction.SWAP]
          i := i + 1
        | "RET" =>
          instructions := instructions ++ [Instruction.RET]
          i := i + 1
        | _ =>
          IO.eprintln s!"Unknown instruction: {op}"
          IO.Process.exit 1
      | _ =>
        i := i + 1
    pure instructions

  /-- Execute a program -/
  executeProgram (program : List Instruction) (state : VMState) : IO VMState := do
    if state.pc >= program.length || state.gas == 0 then
      pure state
    else
      match program.get? state.pc with
      | none => pure state
      | some inst =>
        let (newState, opName) ← executeInstruction inst state
        let traceEntry := (state.pc, opName, newState.stack)
        let tracedState := { newState with
          trace := state.trace ++ [traceEntry]
          gas := state.gas - 1
        }
        if inst == Instruction.RET then
          pure tracedState
        else
          executeProgram program tracedState

  /-- Execute a single instruction -/
  executeInstruction (inst : Instruction) (state : VMState) : IO (VMState × String) := do
    match inst with
    | Instruction.PUSH val =>
      pure ({ state with
        stack := val :: state.stack
        pc := state.pc + 1
      }, s!"PUSH {val}")

    | Instruction.POP =>
      match state.stack with
      | [] => pure (state, "POP (empty)")
      | _ :: rest => pure ({ state with
        stack := rest
        pc := state.pc + 1
      }, "POP")

    | Instruction.AND =>
      match state.stack with
      | b1 :: b2 :: rest =>
        pure ({ state with
          stack := (b1 && b2) :: rest
          pc := state.pc + 1
        }, "AND")
      | _ => pure (state, "AND (underflow)")

    | Instruction.OR =>
      match state.stack with
      | b1 :: b2 :: rest =>
        pure ({ state with
          stack := (b1 || b2) :: rest
          pc := state.pc + 1
        }, "OR")
      | _ => pure (state, "OR (underflow)")

    | Instruction.NOT =>
      match state.stack with
      | b :: rest =>
        pure ({ state with
          stack := (!b) :: rest
          pc := state.pc + 1
        }, "NOT")
      | _ => pure (state, "NOT (underflow)")

    | Instruction.DUP =>
      match state.stack with
      | b :: _ =>
        pure ({ state with
          stack := b :: state.stack
          pc := state.pc + 1
        }, "DUP")
      | _ => pure (state, "DUP (underflow)")

    | Instruction.SWAP =>
      match state.stack with
      | b1 :: b2 :: rest =>
        pure ({ state with
          stack := b2 :: b1 :: rest
          pc := state.pc + 1
        }, "SWAP")
      | _ => pure (state, "SWAP (underflow)")

    | Instruction.RET =>
      pure (state, "RET")

    | Instruction.JMP offset =>
      pure ({ state with
        pc := (state.pc.toInt + offset).toNat
      }, s!"JMP {offset}")

    | Instruction.JZ offset =>
      match state.stack with
      | false :: rest =>
        pure ({ state with
          stack := rest
          pc := (state.pc.toInt + offset).toNat
        }, s!"JZ {offset} (taken)")
      | true :: rest =>
        pure ({ state with
          stack := rest
          pc := state.pc + 1
        }, s!"JZ {offset} (not taken)")
      | _ => pure (state, "JZ (underflow)")