namespace HeytingLean.CLI.VerifierInferFixture

inductive TinyAgent where
  | app
  | k
  deriving Repr, DecidableEq, Inhabited

def TinyAgent.arity : TinyAgent → Nat
  | .app => 2
  | .k => 0

structure TinyNode where
  kind : TinyAgent
  deriving Repr, Inhabited

def auxPortCount (node : TinyNode) : Nat :=
  node.kind.arity

def mkAppNode : TinyNode :=
  { kind := .app }

def auxPortCountFromCtor : Nat :=
  auxPortCount mkAppNode

end HeytingLean.CLI.VerifierInferFixture
