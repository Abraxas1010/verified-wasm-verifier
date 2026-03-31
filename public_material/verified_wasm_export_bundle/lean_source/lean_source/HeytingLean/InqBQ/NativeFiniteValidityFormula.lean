import HeytingLean.InqBQ.FiniteValidityBridge
import HeytingLean.InqBQ.NonRE

namespace HeytingLean
namespace InqBQ

/--
Binary-signature classical surface used by the H10UPC -> finite-validity reduction.
-/
def ReductionSig : Signature where
  PredSym := PUnit
  RigidFun := PEmpty
  NonRigidFun := PEmpty
  predArity _ := 2
  rigidArity := by
    intro f
    cases f
  nonrigidArity := by
    intro f
    cases f

namespace NativeFiniteValidity

/--
Small de Bruijn source syntax matching the Coq-side binary-relation formulas used
by `H10UPC_to_FSAT`.
-/
inductive DBFormula : Type where
  | rel : Nat → Nat → DBFormula
  | bot : DBFormula
  | conj : DBFormula → DBFormula → DBFormula
  | imp : DBFormula → DBFormula → DBFormula
  | all : DBFormula → DBFormula
  | ex : DBFormula → DBFormula

namespace DBFormula

def neg (φ : DBFormula) : DBFormula :=
  .imp φ .bot

def iff_ (φ ψ : DBFormula) : DBFormula :=
  .conj (.imp φ ψ) (.imp ψ φ)

def conjs : List DBFormula → DBFormula
  | [] => .imp .bot .bot
  | φ :: [] => φ
  | φ :: ψs => .conj φ (conjs ψs)

def dbIndex (depth idx : Nat) : Nat :=
  depth - idx - 1

def pairArgs (t u : Term ReductionSig) : Fin 2 → Term ReductionSig
  | ⟨0, _⟩ => t
  | ⟨1, _⟩ => u

def toLocal : Nat → DBFormula → Formula ReductionSig
  | depth, .rel a b =>
      .pred PUnit.unit (pairArgs (.var (dbIndex depth a)) (.var (dbIndex depth b)))
  | _depth, .bot => .bot
  | depth, .conj φ ψ => .conj (toLocal depth φ) (toLocal depth ψ)
  | depth, .imp φ ψ => .imp (toLocal depth φ) (toLocal depth ψ)
  | depth, .all φ => .forall_ depth (toLocal (depth + 1) φ)
  | depth, .ex φ => Formula.classicalExists depth (toLocal (depth + 1) φ)

theorem toLocal_isClassical : ∀ depth φ, Formula.isClassical (toLocal depth φ)
  | _, .rel _ _ => trivial
  | _, .bot => trivial
  | depth, .conj φ ψ => And.intro (toLocal_isClassical depth φ) (toLocal_isClassical depth ψ)
  | depth, .imp φ ψ => And.intro (toLocal_isClassical depth φ) (toLocal_isClassical depth ψ)
  | depth, .all φ => toLocal_isClassical (depth + 1) φ
  | depth, .ex φ =>
      by
        dsimp [toLocal, Formula.classicalExists, Formula.neg, Formula.isClassical]
        exact And.intro (And.intro (toLocal_isClassical (depth + 1) φ) trivial) trivial

def N (a : Nat) : DBFormula :=
  .rel a a

def leq (a b : Nat) : DBFormula :=
  conjs [N a, N b, .rel a b]

def P' (a : Nat) : DBFormula :=
  neg (N a)

def P (p a b : Nat) : DBFormula :=
  conjs [P' p, N a, N b, .rel a p, .rel p b]

def deq (a b : Nat) : DBFormula :=
  .all <|
    .conj
      (iff_ (.rel 0 (Nat.succ a)) (.rel 0 (Nat.succ b)))
      (iff_ (.rel (Nat.succ a) 0) (.rel (Nat.succ b) 0))

def less (a b : Nat) : DBFormula :=
  .conj (leq a b) (neg (deq a b))

def relQuad (a b c d : Nat) : DBFormula :=
  .ex <| .ex <|
    conjs
      [P 1 (2 + a) (2 + b), P 0 (2 + c) (2 + d), .rel 1 0]

def succ (l r z : Nat) : DBFormula :=
  relQuad l z r z

def aTrans : DBFormula :=
  .all <| .all <| .all <|
    .imp (less 2 1) (.imp (less 1 0) (less 2 0))

def aPred (z : Nat) : DBFormula :=
  .all <|
    .imp (N 0)
      (.imp (neg (deq (Nat.succ z) 0))
        (.ex (succ 0 1 (2 + z))))

def aSucc (z : Nat) : DBFormula :=
  .all <| .all <|
    .imp (N 1)
      (.imp (N 0)
        (.imp (relQuad 1 (2 + z) 0 (2 + z))
          (.conj (less 1 0)
            (.all (.imp (less 0 1) (leq 0 2))))))

def aDescr (z : Nat) : DBFormula :=
  .all <| .all <| .all <| .all <|
    .imp (N 3)
      (.imp (N 2)
        (.imp (N 1)
          (.imp (N 0)
            (.imp (neg (deq (4 + z) 2))
              (.imp (relQuad 3 2 1 0)
                (.ex <| .ex <| .ex <|
                  conjs
                    [succ 2 5 (7 + z),
                     succ 1 4 (7 + z),
                     relQuad 0 2 3 0,
                     relQuad 6 2 1 0,
                     less 0 3]))))))

def aDescr2 (z : Nat) : DBFormula :=
  .all <| .all <| .all <| .all <|
    .imp (N 3)
      (.imp (N 2)
        (.imp (N 1)
          (.imp (N 0)
            (.imp (relQuad 3 2 1 0)
              (.imp (deq 2 (4 + z)) (deq 0 (4 + z)))))))

def emplaceExists : Nat → DBFormula → DBFormula
  | 0, φ => φ
  | n + 1, φ => .ex (emplaceExists n φ)

def translateSingle (h : H10UPC) (m : Nat) : DBFormula :=
  match h with
  | ((a, b), (c, d)) =>
      conjs [relQuad a b c d, leq a m, leq b m, leq c m, leq d m]

def translateList (m : Nat) : List H10UPC → DBFormula
  | [] => .imp .bot .bot
  | h :: hs => .conj (translateSingle h m) (translateList m hs)

def sourceF (cs : List H10UPC) : DBFormula :=
  .ex <| .ex <|
    conjs
      [aTrans,
       aPred 1,
       aSucc 1,
       aDescr 1,
       aDescr2 1,
       emplaceExists (Nat.succ (highestVarList cs))
         (translateList (Nat.succ (highestVarList cs)) cs)]

def sourceReductionFormula (cs : List H10UPC) : DBFormula :=
  .imp (sourceF cs) .bot

end DBFormula

end NativeFiniteValidity

/--
Native Lean reconstruction of the classical formula family behind the external
H10UPC -> finite-validity reduction. The remaining trust surface is the
correctness theorem, not the formula construction.
-/
def h10upcFiniteValidityFormula (cs : List H10UPC) : Formula ReductionSig :=
  NativeFiniteValidity.DBFormula.toLocal 0
    (NativeFiniteValidity.DBFormula.sourceReductionFormula cs)

theorem h10upcFiniteValidityFormula_classical (cs : List H10UPC) :
    Formula.isClassical (h10upcFiniteValidityFormula cs) :=
  NativeFiniteValidity.DBFormula.toLocal_isClassical 0
    (NativeFiniteValidity.DBFormula.sourceReductionFormula cs)

end InqBQ
end HeytingLean
