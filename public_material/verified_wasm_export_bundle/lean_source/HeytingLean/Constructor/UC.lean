namespace HeytingLean
namespace Constructor

/-!
# Universal Constructor scaffold (substrate-agnostic)

Abstract scaffold for Universal Constructors (UC) over a generic configuration
space, independent of any particular physical or computational substrate.
-/

/-- Placeholder type of program codes / descriptions. Concrete substrates
can refine this via parameters or dedicated code types. -/
inductive Code : Type
  | mk : Nat → Code

/-- Minimal configuration for a universal constructor: a control state and
a tape carrying codes. Substrate-specific instances are expected to refine
this structure. -/
structure Config where
  state : Nat
  tape  : List Code

/-- Abstract run relation: in this scaffold, `runsTo` is left as an always
true predicate so that the universal-constructor interface type-checks
without committing to a specific dynamics. Concrete adapters should replace
this with the appropriate step semantics. -/
def runsTo : Code → Config → Config → Prop :=
  fun _ _ _ => True

/-- Predicate expressing that a configuration's tape contains a given code. -/
def tapeContains (cfg : Config) (c : Code) : Prop :=
  c ∈ cfg.tape

/-- A Universal Constructor, abstractly:

* `code`    : its own program description,
* `init`    : an initial configuration,
* `selfRepro` : existence of a run and final configuration whose tape
  contains a copy of the constructor's code. -/
structure UC where
  code     : Code
  init     : Config
  selfRepro :
    ∃ final : Config,
      runsTo code init final ∧
      tapeContains final code

end Constructor
end HeytingLean
