import HeytingLean.Numbers.Surreal.PreLegalGame
import HeytingLean.Numbers.Surreal.BidirectionalProof
import HeytingLean.Numbers.Surreal.LoFProgram

/-!
# Surreal.DialecticaBridge

SN-016 baseline: bridge pre-legal strategy objects into the existing
forward/backward Dialectica witness-challenge protocol.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace DialecticaBridge

open HeytingLean.Numbers.Surreal.BidirectionalProof
open HeytingLean.Numbers.Surreal.LoFProgram

/-- Deterministic fallback used only if a compiled program would be empty. -/
private def fallbackProgram : Program :=
  { ops := #[Op.unmark]
    root := 0 }

/-- Ensure program root is in range and `ops` is non-empty. -/
private def sanitizeProgram (p : Program) : Program :=
  if _ : p.ops.size = 0 then
    fallbackProgram
  else
    { ops := p.ops
      root := if _ : p.root < p.ops.size then p.root else 0 }

private theorem sanitizeProgram_root_lt_size (p : Program) :
    (sanitizeProgram p).root < (sanitizeProgram p).ops.size := by
  by_cases hsz : p.ops.size = 0
  · simp [sanitizeProgram, hsz, fallbackProgram]
  · by_cases hroot : p.root < p.ops.size
    · simp [sanitizeProgram, hsz, hroot]
    · have hpos : 0 < p.ops.size := Nat.pos_of_ne_zero hsz
      simp [sanitizeProgram, hsz, hroot, hpos]

/-- Non-toy extraction: compile the pre-legal cut into the LoF DSL, then sanitize. -/
def toProgram (g : PreLegalGame) : Program :=
  sanitizeProgram (LoFProgram.Compile.compile g.toPreGame)

@[simp] theorem toProgram_root_lt_size (g : PreLegalGame) :
    (toProgram g).root < (toProgram g).ops.size := by
  exact sanitizeProgram_root_lt_size _

/-- Build a Dialectica witness from a pre-legal game via forward artifact generation. -/
noncomputable def toWitness (g : PreLegalGame) : Except String DialecticaWitness := do
  let fwd ← forward (toProgram g)
  pure { forward := fwd }

/-- Default challenge used for bridge-level roundtrip checks. -/
def defaultChallenge : DialecticaChallenge :=
  { query := {} }

/-- Run the witness/challenge roundtrip and report verifier status. -/
noncomputable def roundtripOk (g : PreLegalGame) : Except String Bool := do
  let w ← toWitness g
  let rep := dialecticaRespond w defaultChallenge
  pure rep.ok

/-- Gluing a singleton witness family is identity. -/
theorem glue_singleton (w : DialecticaWitness) :
    glueWitnesses [w] = .ok w := by
  rfl

end DialecticaBridge
end Surreal
end Numbers
end HeytingLean
