import HeytingLean.Genesis.EigenformSoup.NucleusPolicy
import HeytingLean.Genesis.Iterant

open scoped Classical

/-!
# Genesis.EigenformSoup.Substrate

WS1 substrate core:
- oscillatory element carrier,
- deterministic expression pool,
- deterministic non-fixed substrate generation.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Stable identifier for substrate elements. -/
abbrev OscId : Type := Nat

/-- Two-phase oscillator labels (aligned with Genesis iterant I/J convention). -/
inductive Phase
  | i
  | j
deriving DecidableEq, Repr

/-- Deterministic phase assignment from id parity. -/
def phaseOfId (id : OscId) : Phase :=
  if id % 2 = 0 then .i else .j

/-- One-step phase update. -/
def nextPhase : Phase → Phase
  | .i => .j
  | .j => .i

/-- One oscillatory candidate carried through soup transitions. -/
structure OscElement (nuc : SoupNucleus) where
  id : OscId
  expr : HeytingLean.Genesis.LoFExpr0
  support : Support
  phase : Phase
  nonFixed : isNonFixed nuc support

/-- Configuration for deterministic substrate generation. -/
structure SubstrateConfig where
  maxDepth : Nat := 4
  size : Nat := 16
deriving Repr

/-- Concrete substrate for a chosen nucleus and generation config. -/
structure Substrate (nuc : SoupNucleus) where
  cfg : SubstrateConfig
  elements : List (OscElement nuc)

/-- Deterministic finite LoF expression pool used by substrate generation. -/
def exprPool (cfg : SubstrateConfig) : List HeytingLean.Genesis.LoFExpr0 :=
  (List.range (cfg.maxDepth + 1)).map HeytingLean.Genesis.nesting ++
    (List.range cfg.maxDepth).map
      (fun n => HeytingLean.LoF.LoFSecond.Expr.mark (HeytingLean.Genesis.nesting n))

/-- Deterministically pick one expression from the finite pool by index. -/
def exprAt (cfg : SubstrateConfig) (id : Nat) : HeytingLean.Genesis.LoFExpr0 :=
  let pool := exprPool cfg
  let idx := id % (Nat.max 1 pool.length)
  (pool[idx]?).getD .void

/-- Attempt to create one oscillatory element from a pooled expression. -/
noncomputable def mkOscElement?
    (nuc : SoupNucleus) (id : OscId) (expr : HeytingLean.Genesis.LoFExpr0) :
    Option (OscElement nuc) :=
  let S := HeytingLean.Genesis.exprSupport expr
  if hFix : isFixed nuc S then
    none
  else
    some
      { id := id
        expr := expr
        support := S
        phase := phaseOfId id
        nonFixed := hFix }

/-- Deterministic non-fixed element generation from indexed pool access. -/
noncomputable def generateElementsAux
    (nuc : SoupNucleus)
    (cfg : SubstrateConfig) : Nat → Nat → List (OscElement nuc)
  | 0, _id => []
  | Nat.succ fuel, id =>
      let expr := exprAt cfg id
      match mkOscElement? nuc id expr with
      | some el => el :: generateElementsAux nuc cfg fuel (id + 1)
      | none => generateElementsAux nuc cfg fuel (id + 1)

/-- Deterministic non-fixed element generation from the finite expression pool. -/
noncomputable def generateElements (nuc : SoupNucleus) (cfg : SubstrateConfig) :
    List (OscElement nuc) :=
  generateElementsAux nuc cfg cfg.size 0

/-- Bundle generated elements with configuration into a substrate value. -/
noncomputable def buildSubstrate (nuc : SoupNucleus) (cfg : SubstrateConfig) : Substrate nuc :=
  { cfg := cfg
    elements := generateElements nuc cfg }

theorem mem_generateElements_nonFixed
    {nuc : SoupNucleus} {cfg : SubstrateConfig} {x : OscElement nuc}
    (_hx : x ∈ generateElements nuc cfg) : isNonFixed nuc x.support :=
  x.nonFixed

theorem generateElements_deterministic (nuc : SoupNucleus) (cfg : SubstrateConfig) :
    generateElements nuc cfg = generateElements nuc cfg := rfl

theorem buildSubstrate_cfg (nuc : SoupNucleus) (cfg : SubstrateConfig) :
    (buildSubstrate nuc cfg).cfg = cfg := rfl

end HeytingLean.Genesis.EigenformSoup
