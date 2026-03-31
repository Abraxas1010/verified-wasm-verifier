import Std.Data.HashMap
import HeytingLean.LoF.Combinators.GraphReduction

/-!
# SKYMachineBounded — bounded heap+stack abstract machine for SKY(+oracle)

This file provides a small deterministic abstract machine suitable as a *hardware spec*:

* heap: an `Array` of `SKYGraph.Node` (used prefix),
* focus: a node id,
* stack: pending argument node ids (spine stack),
* step: leftmost-outermost weak-head reduction (K/S/Y + oracle_select),
* resource bounds: compilation and runtime allocation are capped by `maxNodes`.

It is intended to support an FPGA demo by exporting:
1) an initial heap image,
2) an oracle circuit (AIGER), and
3) an expected output / trace computed by this reference model.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

open HeytingLean.LoF

namespace SKYMachineBounded

open SKYGraph

structure State (OracleRef : Type) where
  nodes : Array (Node OracleRef)
  focus : NodeId
  stack : List NodeId
deriving Repr

namespace State

variable {OracleRef : Type}

def node? (s : State OracleRef) (i : NodeId) : Option (Node OracleRef) :=
  s.nodes[i]?

def pushNode (maxNodes : Nat) (s : State OracleRef) (n : Node OracleRef) : Option (State OracleRef × NodeId) :=
  if s.nodes.size < maxNodes then
    let id := s.nodes.size
    some ({ s with nodes := s.nodes.push n }, id)
  else
    none

private def compileAux (maxNodes : Nat) (nodes : Array (Node OracleRef)) (t : Comb) :
    Option (Array (Node OracleRef) × NodeId) :=
  match t with
  | .K =>
      if nodes.size < maxNodes then
        let id := nodes.size
        some (nodes.push (.combK (OracleRef := OracleRef)), id)
      else
        none
  | .S =>
      if nodes.size < maxNodes then
        let id := nodes.size
        some (nodes.push (.combS (OracleRef := OracleRef)), id)
      else
        none
  | .Y =>
      if nodes.size < maxNodes then
        let id := nodes.size
        some (nodes.push (.combY (OracleRef := OracleRef)), id)
      else
        none
  | .app f a => do
      let (nodes1, fId) <- compileAux maxNodes nodes f
      let (nodes2, aId) <- compileAux maxNodes nodes1 a
      if nodes2.size < maxNodes then
        let id := nodes2.size
        some (nodes2.push (.app (OracleRef := OracleRef) fId aId), id)
      else
        none

/--
Compile a `Comb` term into a bounded machine heap while sharing structurally
equal subterms. The machine never mutates previously allocated nodes, so
reusing an identical subtree is semantically safe and dramatically reduces the
initial heap blow-up for large decoder terms.
-/
private def compileAuxShared
    (maxNodes : Nat)
    (nodes : Array (Node OracleRef))
    (cache : Std.HashMap Comb NodeId)
    (t : Comb) :
    Option (Array (Node OracleRef) × Std.HashMap Comb NodeId × NodeId) := do
  match cache.get? t with
  | some id =>
      pure (nodes, cache, id)
  | none =>
      match t with
      | .K =>
          if nodes.size < maxNodes then
            let id := nodes.size
            let nodes' := nodes.push (.combK (OracleRef := OracleRef))
            pure (nodes', cache.insert t id, id)
          else
            none
      | .S =>
          if nodes.size < maxNodes then
            let id := nodes.size
            let nodes' := nodes.push (.combS (OracleRef := OracleRef))
            pure (nodes', cache.insert t id, id)
          else
            none
      | .Y =>
          if nodes.size < maxNodes then
            let id := nodes.size
            let nodes' := nodes.push (.combY (OracleRef := OracleRef))
            pure (nodes', cache.insert t id, id)
          else
            none
      | .app f a => do
          let (nodes1, cache1, fId) <- compileAuxShared maxNodes nodes cache f
          let (nodes2, cache2, aId) <- compileAuxShared maxNodes nodes1 cache1 a
          match cache2.get? t with
          | some id =>
              pure (nodes2, cache2, id)
          | none =>
              if nodes2.size < maxNodes then
                let id := nodes2.size
                let nodes' := nodes2.push (.app (OracleRef := OracleRef) fId aId)
                pure (nodes', cache2.insert t id, id)
              else
                none

private def requiredNodesAux
    (cache : Std.HashMap Comb NodeId)
    (nextId : Nat)
    (t : Comb) :
    Std.HashMap Comb NodeId × Nat :=
  match cache.get? t with
  | some _ =>
      (cache, nextId)
  | none =>
      match t with
      | .K | .S | .Y =>
          (cache.insert t nextId, nextId + 1)
      | .app f a =>
          let (cache1, nextId1) := requiredNodesAux cache nextId f
          let (cache2, nextId2) := requiredNodesAux cache1 nextId1 a
          match cache2.get? t with
          | some _ =>
              (cache2, nextId2)
          | none =>
              (cache2.insert t nextId2, nextId2 + 1)

/-- Number of heap nodes needed to compile `t` with maximal structural sharing. -/
def requiredNodes (t : Comb) : Nat :=
  let (_cache, nextId) := requiredNodesAux {} 0 t
  nextId

def compileComb? (maxNodes : Nat) (t : Comb) : Option (State OracleRef) := do
  let (nodes, _cache, root) <-
    compileAuxShared (OracleRef := OracleRef) maxNodes #[] {} t
  some { nodes := nodes, focus := root, stack := [] }

def wrapOracleSelect (maxNodes : Nat) (s : State OracleRef) (ref : OracleRef)
    (thenTerm elseTerm : Comb) : Option (State OracleRef) := do
  let (nodes1, thenId) <- compileAux (OracleRef := OracleRef) maxNodes s.nodes thenTerm
  let (nodes2, elseId) <- compileAux (OracleRef := OracleRef) maxNodes nodes1 elseTerm
  let base : State OracleRef := { s with nodes := nodes2 }
  let (s1, oId) <- base.pushNode maxNodes (.oracle (OracleRef := OracleRef) ref)
  let (s2, leftId) <- s1.pushNode maxNodes (.app (OracleRef := OracleRef) oId thenId)
  let (s3, rootId) <- s2.pushNode maxNodes (.app (OracleRef := OracleRef) leftId elseId)
  some { s3 with focus := rootId, stack := [] }

inductive StepResult (OracleRef : Type) where
  | progress (s' : State OracleRef)
  | halted (s : State OracleRef)
  | outOfHeap (s : State OracleRef)
deriving Repr

inductive RunStatus where
  | progress
  | halted
  | outOfHeap
deriving Repr

structure FuelRun (OracleRef : Type) where
  state : State OracleRef
  steps : Nat
  maxStack : Nat
  maxNodesUsed : Nat
  status : RunStatus
deriving Repr

def step (oracleEval : OracleRef → Bool) (maxNodes : Nat) (s : State OracleRef) : StepResult OracleRef :=
  match s.node? s.focus with
  | some (.app f a) =>
      StepResult.progress { s with focus := f, stack := a :: s.stack }
  | some (.combK) =>
      match s.stack with
      | x :: _y :: rest => StepResult.progress { s with focus := x, stack := rest }
      | _ => StepResult.halted s
  | some (.combS) =>
      match s.stack with
      | x :: y :: z :: rest =>
          match s.pushNode maxNodes (.app (OracleRef := OracleRef) x z) with
          | none => StepResult.outOfHeap s
          | some (s1, xz) =>
              match s1.pushNode maxNodes (.app (OracleRef := OracleRef) y z) with
              | none => StepResult.outOfHeap s
              | some (s2, yz) =>
                  match s2.pushNode maxNodes (.app (OracleRef := OracleRef) xz yz) with
                  | none => StepResult.outOfHeap s
                  | some (s3, out) => StepResult.progress { s3 with focus := out, stack := rest }
      | _ => StepResult.halted s
  | some (.combY) =>
      match s.stack with
      | f :: rest =>
          match s.pushNode maxNodes (.app (OracleRef := OracleRef) s.focus f) with
          | none => StepResult.outOfHeap s
          | some (s1, self) =>
              match s1.pushNode maxNodes (.app (OracleRef := OracleRef) f self) with
              | none => StepResult.outOfHeap s
              | some (s2, out) => StepResult.progress { s2 with focus := out, stack := rest }
      | _ => StepResult.halted s
  | some (.oracle ref) =>
      match s.stack with
      | t :: f :: rest =>
          let next := if oracleEval ref then t else f
          StepResult.progress { s with focus := next, stack := rest }
      | _ => StepResult.halted s
  | none => StepResult.halted s

def runFuel (oracleEval : OracleRef → Bool) (maxNodes fuel : Nat) (s : State OracleRef) :
    StepResult OracleRef :=
  match fuel with
  | 0 => StepResult.halted s
  | Nat.succ n =>
      match step oracleEval maxNodes s with
      | StepResult.progress s' => runFuel oracleEval maxNodes n s'
      | StepResult.halted s' => StepResult.halted s'
      | StepResult.outOfHeap s' => StepResult.outOfHeap s'

def runFuelCount (oracleEval : OracleRef → Bool) (maxNodes fuel : Nat) (s : State OracleRef) :
    FuelRun OracleRef :=
  let rec go (remaining steps maxStack maxNodesUsed : Nat) (s : State OracleRef) :
      FuelRun OracleRef :=
    match remaining with
    | 0 =>
        { state := s
          steps := steps
          maxStack := maxStack
          maxNodesUsed := maxNodesUsed
          status := .progress }
    | Nat.succ n =>
        match step oracleEval maxNodes s with
        | .progress s' =>
            go n
              (steps + 1)
              (Nat.max maxStack s'.stack.length)
              (Nat.max maxNodesUsed s'.nodes.size)
              s'
        | .halted s' =>
            { state := s'
              steps := steps
              maxStack := maxStack
              maxNodesUsed := maxNodesUsed
              status := .halted }
        | .outOfHeap s' =>
            { state := s'
              steps := steps
              maxStack := maxStack
              maxNodesUsed := maxNodesUsed
              status := .outOfHeap }
  go fuel 0 s.stack.length s.nodes.size s

def headTag? (s : State OracleRef) : Option String :=
  match s.node? s.focus with
  | some (.combK) => some "K"
  | some (.combS) => some "S"
  | some (.combY) => some "Y"
  | some (.app ..) => some "app"
  | some (.oracle ..) => some "oracle"
  | none => none

end State

end SKYMachineBounded

end Combinators
end LoF
end HeytingLean
