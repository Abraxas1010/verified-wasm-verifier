import HeytingLean.InqBQ.Classical

namespace HeytingLean
namespace InqBQ

open Set

/-- The two non-rigid constants of the witness signature. -/
inductive ABConst where
  | a
  | b
  deriving DecidableEq, Repr

/-- The witness signature with only the non-rigid constants `a` and `b`. -/
def SigmaAB : Signature where
  PredSym := PEmpty
  RigidFun := PEmpty
  NonRigidFun := ABConst
  predArity := PEmpty.elim
  rigidArity := PEmpty.elim
  nonrigidArity := fun _ => 0

namespace SigmaAB

def noArgs {α : Type*} : Fin 0 → α := Fin.elim0

def termA : Term SigmaAB :=
  .nonrigidApp ABConst.a noArgs

def termB : Term SigmaAB :=
  .nonrigidApp ABConst.b noArgs

end SigmaAB

open SigmaAB

/-- The pair of values picked out by the non-rigid constants at a world. -/
def associatedPair (M : InfoModel SigmaAB) (w : M.W) : M.D × M.D :=
  (M.nonrigidInterp w ABConst.a noArgs, M.nonrigidInterp w ABConst.b noArgs)

/-- The relation induced by a state through the non-rigid constants `a` and `b`. -/
def associatedRelation (M : InfoModel SigmaAB) (s : Set M.W) : Set (M.D × M.D) :=
  { p | ∃ w ∈ s, associatedPair M w = p }

/-- Fullness means that the induced relation over the total state is all of `D × D`. -/
def isFull (M : InfoModel SigmaAB) : Prop :=
  associatedRelation M Set.univ = Set.univ

/-- Canonical full id-model over a nonempty domain. Worlds are ordered pairs. -/
def canonicalFull (D : Type) [Nonempty D] : InfoModel SigmaAB where
  W := D × D
  D := D
  hW := inferInstance
  hD := inferInstance
  predInterp := fun w P => PEmpty.elim P
  rigidInterp := fun f => PEmpty.elim f
  nonrigidInterp := fun w f _ =>
    match f with
    | .a => w.1
    | .b => w.2
  localEq := fun _ x y => x = y
  localEq_equiv := by
    intro w
    exact ⟨fun x => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  localEq_congr_pred := by
    intro w P
    exact PEmpty.elim P
  localEq_congr_rigid := by
    intro w f
    exact PEmpty.elim f
  localEq_congr_nonrigid := by
    intro w f xs ys hxy
    cases f <;> rfl

theorem canonicalFull_isIdModel (D : Type) [Nonempty D] :
    (canonicalFull D).isIdModel := by
  intro w d d'
  rfl

theorem canonicalFull_isFull (D : Type) [Nonempty D] :
    isFull (canonicalFull D) := by
  ext p
  constructor
  · intro hp
    simp
  · intro hp
    rcases p with ⟨d, e⟩
    refine ⟨(d, e), ?_, rfl⟩
    simp

end InqBQ
end HeytingLean
