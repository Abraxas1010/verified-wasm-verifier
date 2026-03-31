namespace HeytingLean.Bridge.Solvers

/-- SMT-LIB2 sort representation -/
inductive SMTSort where
  | bool : SMTSort
  | int : SMTSort
  | real : SMTSort
  | bitvec : Nat → SMTSort
  | array : SMTSort → SMTSort → SMTSort
  deriving Repr

/-- SMT-LIB2 term representation -/
inductive SMTTerm where
  | const : String → SMTSort → SMTTerm
  | app : String → List SMTTerm → SMTTerm
  | lit : Int → SMTTerm
  | bvlit : Nat → Nat → SMTTerm
  | raw : String → SMTTerm
  deriving Repr

/-- Emit an SMT-LIB2 term string from a structured term. -/
def emitSMTLIB2 (t : SMTTerm) : String :=
  match t with
  | .const name _ => name
  | .app fn args => s!"({fn} {" ".intercalate (args.map emitSMTLIB2)})"
  | .lit n => toString n
  | .bvlit w v => s!"(_ bv{v} {w})"
  | .raw s => s

/-- Wrap a term in a complete SMT-LIB2 query -/
def wrapQuery (logic : String) (decls : List String) (assertions : List SMTTerm) : String :=
  let header := s!"(set-logic {logic})\n"
  let declBlock := "\n".intercalate decls
  let assertBlock := "\n".intercalate (assertions.map fun t => s!"(assert {emitSMTLIB2 t})")
  s!"{header}{declBlock}\n{assertBlock}\n(check-sat)\n(get-model)"

end HeytingLean.Bridge.Solvers
