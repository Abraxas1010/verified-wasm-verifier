import HeytingLean.Numbers.SurrealCore
import HeytingLean.Numbers.Surreal.Equiv
import HeytingLean.Numbers.Surreal.GameN
import HeytingLean.Numbers.Surreal.Operations
import HeytingLean.Numbers.Surreal.QuotCoreSemantics

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore

/-- Canonical base quotient representative used by the scaffolded quotient ops. -/
noncomputable def baseQ : SurrealQ :=
  Quotient.mk (s := approxSetoid) nullCut

/-- Convert a `PreGame` to a `Game`. -/
noncomputable def toGame (g : PreGame) : Game := ofPreGame g

/-- Convert a `Game` back to a `PreGame`. -/
noncomputable def fromGame (g : Game) : PreGame := toPreGame g

/-- Canonical `Game` representative of a quotient surreal. -/
noncomputable def repr (x : SurrealQ) : Game :=
  Quotient.liftOn x toGame (by
    intro a b hab
    have hab' : canonicalize a = canonicalize b := hab
    simpa [canonicalize] using congrArg toGame hab')

/-- Package a `Game` into the quotient. -/
noncomputable def ofGameQ (g : Game) : SurrealQ :=
  Quotient.mk (s := approxSetoid) (canonicalize (fromGame g))

/-- Zero on the quotient. -/
noncomputable def zeroQ : SurrealQ := zeroQCore

/-- Addition on the quotient. -/
noncomputable def addQ (x y : SurrealQ) : SurrealQ :=
  addQCore x y

/-- Negation on the quotient. -/
noncomputable def negQ (x : SurrealQ) : SurrealQ :=
  negQCore x

/-- Multiplication on the quotient. -/
noncomputable def mulQ (x y : SurrealQ) : SurrealQ :=
  mulQCore x y

@[simp] theorem zeroQ_eq_zeroQCore :
    zeroQ = zeroQCore := rfl

@[simp] theorem addQ_eq_addQCore (x y : SurrealQ) :
    addQ x y = addQCore x y := rfl

@[simp] theorem negQ_eq_negQCore (x : SurrealQ) :
    negQ x = negQCore x := rfl

@[simp] theorem mulQ_eq_mulQCore (x y : SurrealQ) :
    mulQ x y = mulQCore x y := rfl

@[simp] theorem coreRepr_zeroQ :
    coreRepr zeroQ = canonicalize SurrealCore.nullCut := by
  simp [zeroQ, zeroQCore, coreRepr_mk, canonicalize_idem]

@[simp] theorem coreRepr_addQ (x y : SurrealQ) :
    coreRepr (addQ x y) = canonicalize (SurrealCore.add (coreRepr x) (coreRepr y)) := by
  simp [addQ, addQCore, coreRepr_mk, canonicalize_idem]

@[simp] theorem coreRepr_negQ (x : SurrealQ) :
    coreRepr (negQ x) = canonicalize (SurrealCore.neg (coreRepr x)) := by
  simp [negQ, negQCore, coreRepr_mk, canonicalize_idem]

@[simp] theorem coreRepr_mulQ (x y : SurrealQ) :
    coreRepr (mulQ x y) = canonicalize (SurrealCore.mul (coreRepr x) (coreRepr y)) := by
  simp [mulQ, mulQCore, coreRepr_mk, canonicalize_idem]

/-- Normalized projection on the quotient. -/
noncomputable def normalizeQ (x : SurrealQ) : SurrealQ :=
  canonicalizeQ x

@[simp] theorem normalizeQ_idem (x : SurrealQ) :
    normalizeQ (normalizeQ x) = normalizeQ x := by
  simp [normalizeQ]

@[simp] theorem canonicalizeQ_ofGame (g : Game) :
    canonicalizeQ (ofGameQ g) = ofGameQ g := by
  change Quotient.mk (s := approxSetoid) (canonicalize (canonicalize (fromGame g))) =
    Quotient.mk (s := approxSetoid) (canonicalize (fromGame g))
  apply Quot.sound
  change canonicalize (canonicalize (canonicalize (fromGame g))) =
    canonicalize (canonicalize (fromGame g))
  simp [canonicalize_idem]

@[simp] theorem canonicalizeQ_zeroQ :
    canonicalizeQ zeroQ = zeroQ := by
  simp [zeroQ]

@[simp] theorem canonicalizeQ_addQ (x y : SurrealQ) :
    canonicalizeQ (addQ x y) = addQ x y := by
  simp [addQ]

@[simp] theorem canonicalizeQ_negQ (x : SurrealQ) :
    canonicalizeQ (negQ x) = negQ x := by
  simp [negQ]

@[simp] theorem canonicalizeQ_mulQ (x y : SurrealQ) :
    canonicalizeQ (mulQ x y) = mulQ x y := by
  simp [mulQ]

@[simp] theorem canonicalizeQ_normalizeQ (x : SurrealQ) :
    canonicalizeQ (normalizeQ x) = normalizeQ x := by
  simp [normalizeQ]

theorem toIGameQ_addQ (x y : SurrealQ) :
    toIGameQ (addQ x y) = toIGameQ x + toIGameQ y := by
  simpa [addQ] using toIGameQ_addQCore x y

theorem toIGameQ_negQ (x : SurrealQ) :
    toIGameQ (negQ x) = -toIGameQ x := by
  simpa [negQ] using toIGameQ_negQCore x

theorem toIGameQ_mulQ (x y : SurrealQ) :
    toIGameQ (mulQ x y) = toIGameQ x * toIGameQ y := by
  simpa [mulQ] using toIGameQ_mulQCore x y

theorem toIGameQ_zeroQ :
    toIGameQ zeroQ = 0 := by
  simpa [zeroQ] using toIGameQ_zeroQCore

theorem toIGameQ_mul_zeroQ_left (x : SurrealQ) :
    toIGameQ (mulQ zeroQ x) = 0 := by
  simpa [mulQ, zeroQ] using toIGameQ_mul_zeroQCore_left x

theorem toIGameQ_mul_zeroQ_right (x : SurrealQ) :
    toIGameQ (mulQ x zeroQ) = 0 := by
  simpa [mulQ, zeroQ] using toIGameQ_mul_zeroQCore_right x

theorem toIGameQ_add_zeroQ_left (x : SurrealQ) :
    toIGameQ (addQ zeroQ x) = toIGameQ x := by
  simpa [addQ, zeroQ] using toIGameQ_add_zeroQCore_left x

theorem toIGameQ_add_zeroQ_right (x : SurrealQ) :
    toIGameQ (addQ x zeroQ) = toIGameQ x := by
  simpa [addQ, zeroQ] using toIGameQ_add_zeroQCore_right x

theorem toIGameQ_mul_addQ_equiv (x y z : SurrealQ) :
    toIGameQ (mulQ x (addQ y z)) ≈
      toIGameQ (addQ (mulQ x y) (mulQ x z)) := by
  simpa [addQ, mulQ] using toIGameQ_mul_addQCore_equiv x y z

theorem toIGameQ_add_mulQ_equiv (x y z : SurrealQ) :
    toIGameQ (mulQ (addQ x y) z) ≈
      toIGameQ (addQ (mulQ x z) (mulQ y z)) := by
  simpa [addQ, mulQ] using toIGameQ_add_mulQCore_equiv x y z

theorem toIGameQ_mulQ_assoc_equiv (x y z : SurrealQ) :
    toIGameQ (mulQ (mulQ x y) z) ≈
      toIGameQ (mulQ x (mulQ y z)) := by
  simpa [mulQ] using toIGameQ_mulQCore_assoc_equiv x y z

theorem toIGameQ_mulQ_comm (x y : SurrealQ) :
    toIGameQ (mulQ x y) = toIGameQ (mulQ y x) := by
  simpa [mulQ] using toIGameQ_mulQCore_comm x y

theorem toIGameQ_addQ_comm (x y : SurrealQ) :
    toIGameQ (addQ x y) = toIGameQ (addQ y x) := by
  simpa [addQ] using toIGameQ_addQCore_comm x y

theorem toIGameQ_addQ_assoc (x y z : SurrealQ) :
    toIGameQ (addQ (addQ x y) z) = toIGameQ (addQ x (addQ y z)) := by
  simpa [addQ] using toIGameQ_addQCore_assoc x y z

theorem toIGameQ_add_left_negQ_equiv_zero (x : SurrealQ) :
    toIGameQ (addQ (negQ x) x) ≈ 0 := by
  simpa [addQ, negQ] using toIGameQ_add_left_negQCore_equiv_zero x

theorem toIGameQ_add_right_negQ_equiv_zero (x : SurrealQ) :
    toIGameQ (addQ x (negQ x)) ≈ 0 := by
  simpa [addQ, negQ] using toIGameQ_add_right_negQCore_equiv_zero x

theorem toIGameQ_add_left_cancelQ_equiv (x y : SurrealQ) :
    toIGameQ (addQ (negQ x) (addQ x y)) ≈ toIGameQ y := by
  simpa [addQ, negQ] using toIGameQ_add_left_cancelQCore_equiv x y

theorem toIGameQ_add_right_cancelQ_equiv (x y : SurrealQ) :
    toIGameQ (addQ x (addQ (negQ x) y)) ≈ toIGameQ y := by
  simpa [addQ, negQ] using toIGameQ_add_right_cancelQCore_equiv x y

end Surreal
end Numbers
end HeytingLean
