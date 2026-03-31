import HeytingLean.InqBQ.H10UPCComputability
import HeytingLean.InqBQ.NativeFiniteValidityFormula
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace HeytingLean
namespace InqBQ
namespace NativeFiniteValidity

open Classical

abbrev RelInterp (S : ClassicalStructure ReductionSig) : S.D → S.D → Prop :=
  fun a b =>
    S.predInterp PUnit.unit
      (fun
        | ⟨0, _⟩ => a
        | ⟨1, _⟩ => b)

def consEnv {α : Type*} (d : α) (ρ : Nat → α) : Nat → α
  | 0 => d
  | n + 1 => ρ n

@[simp] theorem consEnv_zero {α : Type*} (d : α) (ρ : Nat → α) :
    consEnv d ρ 0 = d := rfl

@[simp] theorem consEnv_succ {α : Type*} (d : α) (ρ : Nat → α) (n : Nat) :
    consEnv d ρ (n + 1) = ρ n := rfl

@[simp] theorem consEnv_consEnv_two_add {α : Type*} (d e : α) (ρ : Nat → α) (n : Nat) :
    consEnv d (consEnv e ρ) (n + 2) = ρ n := rfl

def dbSatisfies (S : ClassicalStructure ReductionSig) (ρ : Nat → S.D) :
    DBFormula → Prop
  | .rel a b =>
      RelInterp S (ρ a) (ρ b)
  | .bot =>
      False
  | .conj φ ψ =>
      dbSatisfies S ρ φ ∧ dbSatisfies S ρ ψ
  | .imp φ ψ =>
      dbSatisfies S ρ φ → dbSatisfies S ρ ψ
  | .all φ =>
      ∀ d : S.D, dbSatisfies S (consEnv d ρ) φ
  | .ex φ =>
      ∃ d : S.D, dbSatisfies S (consEnv d ρ) φ

def dbSatisfiesAt (S : ClassicalStructure ReductionSig) (g : Assignment S.D) :
    Nat → DBFormula → Prop
  | depth, .rel a b =>
      RelInterp S (g (DBFormula.dbIndex depth a)) (g (DBFormula.dbIndex depth b))
  | _depth, .bot =>
      False
  | depth, .conj φ ψ =>
      dbSatisfiesAt S g depth φ ∧ dbSatisfiesAt S g depth ψ
  | depth, .imp φ ψ =>
      dbSatisfiesAt S g depth φ → dbSatisfiesAt S g depth ψ
  | depth, .all φ =>
      ∀ d : S.D, dbSatisfiesAt S (Assignment.update g depth d) (depth + 1) φ
  | depth, .ex φ =>
      ∃ d : S.D, dbSatisfiesAt S (Assignment.update g depth d) (depth + 1) φ

def assignOfEnv (S : ClassicalStructure ReductionSig)
    (depth : Nat) (ρ : Nat → S.D) (g : Assignment S.D) : Assignment S.D :=
  fun k => if hk : k < depth then ρ (depth - k - 1) else g k

theorem assignOfEnv_dbIndex
    (S : ClassicalStructure ReductionSig)
    (depth : Nat) (ρ : Nat → S.D) (g : Assignment S.D)
    {a : Nat} (ha : a < depth) :
    assignOfEnv S depth ρ g (DBFormula.dbIndex depth a) = ρ a := by
  have hs : a + 1 ≤ depth := Nat.succ_le_of_lt ha
  have hdb :
      DBFormula.dbIndex depth a + (a + 1) = depth := by
    simpa [DBFormula.dbIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.sub_add_cancel hs
  have hk : DBFormula.dbIndex depth a < depth := by
    have hpos : 0 < a + 1 := Nat.succ_pos a
    have : DBFormula.dbIndex depth a < DBFormula.dbIndex depth a + (a + 1) := by
      exact Nat.lt_add_of_pos_right (n := DBFormula.dbIndex depth a) hpos
    simpa [hdb] using this
  have hInner : depth - DBFormula.dbIndex depth a - 1 = a := by
    change depth - (depth - a - 1) - 1 = a
    omega
  simpa [assignOfEnv, hk, hInner]

theorem assignOfEnv_update
    (S : ClassicalStructure ReductionSig)
    (depth : Nat) (ρ : Nat → S.D) (g : Assignment S.D) (d : S.D) :
    Assignment.update (assignOfEnv S depth ρ g) depth d =
      assignOfEnv S (depth + 1) (consEnv d ρ) g := by
  funext k
  by_cases hk : k < depth
  · have hk' : k ≠ depth := by omega
    have hk1 : k < depth + 1 := by omega
    have harg : depth + 1 - k - 1 = Nat.succ (depth - k - 1) := by
      omega
    simp [assignOfEnv, hk, hk1, Assignment.update, hk', harg]
  · by_cases hEq : k = depth
    · subst hEq
      simp [assignOfEnv, hk, Assignment.update]
    · have hkge : depth + 1 ≤ k := by omega
      have hk1 : ¬ k < depth + 1 := by omega
      simp [assignOfEnv, hk, hk1, Assignment.update, hEq]

def WellScoped : Nat → DBFormula → Prop
  | depth, .rel a b => a < depth ∧ b < depth
  | _depth, .bot => True
  | depth, .conj φ ψ => WellScoped depth φ ∧ WellScoped depth ψ
  | depth, .imp φ ψ => WellScoped depth φ ∧ WellScoped depth ψ
  | depth, .all φ => WellScoped (depth + 1) φ
  | depth, .ex φ => WellScoped (depth + 1) φ

theorem dbSatisfies_iff_dbSatisfiesAt
    (S : ClassicalStructure ReductionSig)
    (depth : Nat) (ρ : Nat → S.D) (g : Assignment S.D) :
    ∀ {φ : DBFormula}, WellScoped depth φ →
      (dbSatisfies S ρ φ ↔ dbSatisfiesAt S (assignOfEnv S depth ρ g) depth φ)
  | .rel a b, hScoped => by
      rcases hScoped with ⟨ha, hb⟩
      simp [dbSatisfies, dbSatisfiesAt,
        assignOfEnv_dbIndex S depth ρ g ha,
        assignOfEnv_dbIndex S depth ρ g hb]
  | .bot, _ => by
      simp [dbSatisfies, dbSatisfiesAt]
  | .conj φ ψ, hScoped => by
      rcases hScoped with ⟨hφ, hψ⟩
      simpa [dbSatisfies, dbSatisfiesAt] using
        Iff.and (dbSatisfies_iff_dbSatisfiesAt S depth ρ g hφ)
          (dbSatisfies_iff_dbSatisfiesAt S depth ρ g hψ)
  | .imp φ ψ, hScoped => by
      rcases hScoped with ⟨hφ, hψ⟩
      simpa [dbSatisfies, dbSatisfiesAt] using
        Iff.imp (dbSatisfies_iff_dbSatisfiesAt S depth ρ g hφ)
          (dbSatisfies_iff_dbSatisfiesAt S depth ρ g hψ)
  | .all φ, hScoped => by
      constructor
      · intro h d
        have hAt :
            dbSatisfiesAt S (assignOfEnv S (depth + 1) (consEnv d ρ) g) (depth + 1) φ :=
          (dbSatisfies_iff_dbSatisfiesAt S (depth + 1) (consEnv d ρ) g hScoped).1 (h d)
        simpa [dbSatisfiesAt, assignOfEnv_update] using hAt
      · intro h d
        have hAt :
            dbSatisfiesAt S (assignOfEnv S (depth + 1) (consEnv d ρ) g) (depth + 1) φ := by
          simpa [dbSatisfiesAt, assignOfEnv_update] using h d
        exact (dbSatisfies_iff_dbSatisfiesAt S (depth + 1) (consEnv d ρ) g hScoped).2 hAt
  | .ex φ, hScoped => by
      constructor
      · rintro ⟨d, hd⟩
        have hAt :
            dbSatisfiesAt S (assignOfEnv S (depth + 1) (consEnv d ρ) g) (depth + 1) φ :=
          (dbSatisfies_iff_dbSatisfiesAt S (depth + 1) (consEnv d ρ) g hScoped).1 hd
        refine ⟨d, ?_⟩
        simpa [dbSatisfiesAt, assignOfEnv_update] using hAt
      · rintro ⟨d, hd⟩
        have hAt :
            dbSatisfiesAt S (assignOfEnv S (depth + 1) (consEnv d ρ) g) (depth + 1) φ := by
          simpa [dbSatisfiesAt, assignOfEnv_update] using hd
        refine ⟨d, ?_⟩
        exact (dbSatisfies_iff_dbSatisfiesAt S (depth + 1) (consEnv d ρ) g hScoped).2 hAt

@[simp] theorem assignOfEnv_zero
    (S : ClassicalStructure ReductionSig)
    (ρ : Nat → S.D) (g : Assignment S.D) :
    assignOfEnv S 0 ρ g = g := by
  funext k
  simp [assignOfEnv]

theorem wellScoped_N {depth a : Nat} (ha : a < depth) :
    WellScoped depth (DBFormula.N a) := by
  simp [DBFormula.N, WellScoped, ha]

theorem wellScoped_P' {depth a : Nat} (ha : a < depth) :
    WellScoped depth (DBFormula.P' a) := by
  simp [DBFormula.P', DBFormula.neg, DBFormula.N, WellScoped, ha]

theorem wellScoped_leq {depth a b : Nat} (ha : a < depth) (hb : b < depth) :
    WellScoped depth (DBFormula.leq a b) := by
  simp [DBFormula.leq, DBFormula.conjs, DBFormula.N, WellScoped, ha, hb]

theorem wellScoped_P {depth p a b : Nat}
    (hp : p < depth) (ha : a < depth) (hb : b < depth) :
    WellScoped depth (DBFormula.P p a b) := by
  simp [DBFormula.P, DBFormula.conjs, WellScoped, hp, ha, hb,
    DBFormula.P', DBFormula.neg, DBFormula.N]

theorem wellScoped_deq {depth a b : Nat} (ha : a < depth) (hb : b < depth) :
    WellScoped depth (DBFormula.deq a b) := by
  simp [DBFormula.deq, DBFormula.iff_, DBFormula.neg, WellScoped]
  omega

theorem wellScoped_less {depth a b : Nat} (ha : a < depth) (hb : b < depth) :
    WellScoped depth (DBFormula.less a b) := by
  refine ⟨wellScoped_leq ha hb, ?_⟩
  simpa [DBFormula.neg, WellScoped] using (wellScoped_deq ha hb)

theorem wellScoped_relQuad {depth a b c d : Nat}
    (ha : a < depth) (hb : b < depth) (hc : c < depth) (hd : d < depth) :
    WellScoped depth (DBFormula.relQuad a b c d) := by
  simp [DBFormula.relQuad, DBFormula.conjs, DBFormula.P, DBFormula.P',
    DBFormula.neg, DBFormula.N, WellScoped]
  omega

theorem wellScoped_succ {depth l r z : Nat}
    (hl : l < depth) (hr : r < depth) (hz : z < depth) :
    WellScoped depth (DBFormula.succ l r z) :=
  wellScoped_relQuad hl hz hr hz

theorem wellScoped_aTrans (depth : Nat) :
    WellScoped depth DBFormula.aTrans := by
  simp [DBFormula.aTrans, DBFormula.less, DBFormula.leq, DBFormula.deq,
    DBFormula.iff_, DBFormula.neg, DBFormula.conjs, DBFormula.N, WellScoped]

theorem wellScoped_aPred {depth z : Nat} (hz : z < depth) :
    WellScoped depth (DBFormula.aPred z) := by
  simp [DBFormula.aPred, DBFormula.neg, DBFormula.succ, DBFormula.relQuad,
    DBFormula.P, DBFormula.P', DBFormula.deq, DBFormula.iff_, DBFormula.conjs,
    DBFormula.N, WellScoped]
  omega

theorem wellScoped_aSucc {depth z : Nat} (hz : z < depth) :
    WellScoped depth (DBFormula.aSucc z) := by
  simp [DBFormula.aSucc, DBFormula.less, DBFormula.leq, DBFormula.deq,
    DBFormula.iff_, DBFormula.neg, DBFormula.succ, DBFormula.relQuad,
    DBFormula.P, DBFormula.P', DBFormula.conjs, DBFormula.N, WellScoped]
  omega

theorem wellScoped_aDescr {depth z : Nat} (hz : z < depth) :
    WellScoped depth (DBFormula.aDescr z) := by
  simp [DBFormula.aDescr, DBFormula.less, DBFormula.leq, DBFormula.deq,
    DBFormula.iff_, DBFormula.neg, DBFormula.succ, DBFormula.relQuad,
    DBFormula.P, DBFormula.P', DBFormula.conjs, DBFormula.N, WellScoped]
  omega

theorem wellScoped_aDescr2 {depth z : Nat} (hz : z < depth) :
    WellScoped depth (DBFormula.aDescr2 z) := by
  simp [DBFormula.aDescr2, DBFormula.deq, DBFormula.iff_, DBFormula.neg,
    DBFormula.relQuad, DBFormula.P, DBFormula.P', DBFormula.conjs, DBFormula.N,
    WellScoped]
  omega

theorem wellScoped_emplaceExists :
    ∀ n depth φ, WellScoped (depth + n) φ → WellScoped depth (DBFormula.emplaceExists n φ)
  | 0, depth, φ, hφ => by
      simpa [DBFormula.emplaceExists] using hφ
  | n + 1, depth, φ, hφ => by
      simp [DBFormula.emplaceExists]
      exact wellScoped_emplaceExists n (depth + 1) φ (by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hφ)

theorem wellScoped_translateSingle
    (depth : Nat) (m : Nat) (c : H10UPC)
    (hc : highestVar c < depth) (hm : m < depth) :
    WellScoped depth (DBFormula.translateSingle c m) := by
  rcases c with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  have ha : a < depth := lt_of_le_of_lt (leftVar_le_highestVar ((a, b), (c, d))) hc
  have hb : b < depth := lt_of_le_of_lt (rightVar_le_highestVar ((a, b), (c, d))) hc
  have hc' : c < depth := lt_of_le_of_lt (thirdVar_le_highestVar ((a, b), (c, d))) hc
  have hd : d < depth := lt_of_le_of_lt (fourthVar_le_highestVar ((a, b), (c, d))) hc
  simpa [DBFormula.translateSingle, DBFormula.conjs] using
    And.intro
      (wellScoped_relQuad ha hb hc' hd)
      (And.intro
        (wellScoped_leq ha hm)
        (And.intro
          (wellScoped_leq hb hm)
          (And.intro
            (wellScoped_leq hc' hm)
            (wellScoped_leq hd hm))))

theorem wellScoped_translateList
    (depth : Nat) (m : Nat) (cs : List H10UPC)
    (hm : m < depth)
    (hcs : ∀ c, c ∈ cs → highestVar c < depth) :
    WellScoped depth (DBFormula.translateList m cs) := by
  revert hm hcs
  induction cs with
  | nil =>
      intro hm hcs
      simp [DBFormula.translateList, WellScoped]
  | cons c cs ih =>
      intro hm hcs
      have hTail : ∀ d, d ∈ cs → highestVar d < depth := by
        intro d hd
        exact hcs d (by simp [hd])
      simpa [DBFormula.translateList, DBFormula.conjs] using
        And.intro
          (wellScoped_translateSingle depth m c (hcs c (by simp)) hm)
          (ih hm hTail)

theorem wellScoped_sourceF (cs : List H10UPC) :
    WellScoped 0 (DBFormula.sourceF cs) := by
  let n := Nat.succ (highestVarList cs)
  have hOne : 1 < 2 := by omega
  have hn : n < 2 + n := by
    dsimp [n]
    omega
  have hTrans :
      WellScoped (2 + n) (DBFormula.translateList n cs) := by
    apply wellScoped_translateList (depth := 2 + n) (m := n) (cs := cs)
    · exact hn
    · intro c hc
      have hMax : highestVar c ≤ highestVarList cs := highestVar_le_highestVarList hc
      dsimp [n]
      omega
  have hEmplace :
      WellScoped 2 (DBFormula.emplaceExists n (DBFormula.translateList n cs)) := by
    exact wellScoped_emplaceExists n 2 _ hTrans
  simpa [DBFormula.sourceF, DBFormula.conjs, n] using
    And.intro
      (wellScoped_aTrans 2)
      (And.intro
        (wellScoped_aPred hOne)
        (And.intro
          (wellScoped_aSucc hOne)
          (And.intro
            (wellScoped_aDescr hOne)
            (And.intro
              (wellScoped_aDescr2 hOne)
              hEmplace))))

theorem wellScoped_sourceReductionFormula (cs : List H10UPC) :
    WellScoped 0 (DBFormula.sourceReductionFormula cs) := by
  simpa [DBFormula.sourceReductionFormula, WellScoped] using
    And.intro (wellScoped_sourceF cs) trivial

theorem dbSatisfiesAt_toLocal_iff
    (S : ClassicalStructure ReductionSig) (g : Assignment S.D) :
    ∀ depth φ,
      ClassicalStructure.satisfies S g (DBFormula.toLocal depth φ) ↔
        dbSatisfiesAt S g depth φ
  | depth, .rel a b => by
      dsimp [DBFormula.toLocal, dbSatisfiesAt, RelInterp, ClassicalStructure.satisfies]
      have hArgs :
          (fun i =>
            S.denote g
              (DBFormula.pairArgs
                (Term.var (DBFormula.dbIndex depth a))
                (Term.var (DBFormula.dbIndex depth b)) i)) =
            (fun x =>
              match x with
              | ⟨0, _⟩ => g (DBFormula.dbIndex depth a)
              | ⟨1, _⟩ => g (DBFormula.dbIndex depth b)) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          refine Fin.cases ?_ ?_ j
          · rfl
          · intro k
            exact Fin.elim0 k
      exact Iff.of_eq (congrArg (S.predInterp PUnit.unit) hArgs)
  | _depth, .bot => by
      simp [DBFormula.toLocal, dbSatisfiesAt, ClassicalStructure.satisfies]
  | depth, .conj φ ψ => by
      simpa [DBFormula.toLocal, dbSatisfiesAt, ClassicalStructure.satisfies,
        dbSatisfiesAt_toLocal_iff]
  | depth, .imp φ ψ => by
      simpa [DBFormula.toLocal, dbSatisfiesAt, ClassicalStructure.satisfies,
        dbSatisfiesAt_toLocal_iff]
  | depth, .all φ => by
      simpa [DBFormula.toLocal, dbSatisfiesAt, ClassicalStructure.satisfies,
        dbSatisfiesAt_toLocal_iff]
  | depth, .ex φ => by
      classical
      simp [DBFormula.toLocal, dbSatisfiesAt, dbSatisfiesAt_toLocal_iff,
        Formula.classicalExists, Formula.neg, ClassicalStructure.satisfies]

theorem dbSatisfies_toLocal_iff
    (S : ClassicalStructure ReductionSig)
    (depth : Nat) (ρ : Nat → S.D) (g : Assignment S.D)
    {φ : DBFormula} (hScoped : WellScoped depth φ) :
    ClassicalStructure.satisfies S (assignOfEnv S depth ρ g) (DBFormula.toLocal depth φ) ↔
      dbSatisfies S ρ φ := by
  exact
    (dbSatisfiesAt_toLocal_iff S (assignOfEnv S depth ρ g) depth φ).trans
      (dbSatisfies_iff_dbSatisfiesAt S depth ρ g hScoped).symm

def canonicalStructure (m : Nat) : ClassicalStructure ReductionSig where
  D := Model m
  hD := ⟨Model.num ⟨0, Nat.zero_le _⟩⟩
  predInterp := by
    intro P args
    cases P
    exact modelRel m (args ⟨0, by decide⟩) (args ⟨1, by decide⟩)
  rigidInterp := by
    intro f
    cases f
  nonrigidInterp := by
    intro f
    cases f

@[simp] theorem relInterp_canonicalStructure (m : Nat) (a b : Model m) :
    RelInterp (canonicalStructure m) a b ↔ modelRel m a b := by
  simp [RelInterp, canonicalStructure]

def intoFin (m k : Nat) : finNum m :=
  if hk : k ≤ m then ⟨k, hk⟩ else ⟨0, Nat.zero_le _⟩

def transportBound (cs : List H10UPC) (ρ : Nat → Nat) : Nat :=
  Nat.succ (highestNum ρ (highestVarList cs))

def transportAssignment (cs : List H10UPC) (ρ : Nat → Nat) :
    Assignment (Model (transportBound cs ρ)) :=
  fun k => Model.num (intoFin (transportBound cs ρ) (ρ k))

theorem le_highestNum (ρ : Nat → Nat) {i n : Nat} (hi : i ≤ n) :
    ρ i ≤ highestNum ρ n := by
  induction n with
  | zero =>
      have : i = 0 := Nat.eq_zero_of_le_zero hi
      subst this
      simp [highestNum]
  | succ n ih =>
      by_cases hEq : i = n + 1
      · subst hEq
        simp [highestNum]
      · have hi' : i ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hi hEq)
        exact le_trans (ih hi') (Nat.le_max_right _ _)

theorem transportAssignment_desc
    (cs : List H10UPC) (ρ : Nat → Nat) (i : Nat) (hi : i ≤ highestVarList cs) :
    ∃ h : ρ i ≤ transportBound cs ρ,
      transportAssignment cs ρ i = Model.num ⟨ρ i, h⟩ := by
  unfold transportAssignment intoFin transportBound
  have hi' : ρ i ≤ Nat.succ (highestNum ρ (highestVarList cs)) := by
    exact Nat.le_succ_of_le (le_highestNum (ρ := ρ) hi)
  simp [hi', transportBound]

theorem h10upcSemDirect_irrefl (a b : Nat) :
    ¬ h10upcSemDirect ((a, b), (a, b)) := by
  intro h
  dsimp [h10upcSemDirect] at h
  omega

theorem dbSatisfies_N_iff
    (m : Nat) (ρ : Nat → Model m) (a : Nat) :
    dbSatisfies (canonicalStructure m) ρ (DBFormula.N a) ↔
      ∃ n : finNum m, ρ a = Model.num n := by
  cases hρ : ρ a with
  | num n =>
      constructor
      · intro _
        exact ⟨n, rfl⟩
      · intro _
        simpa [DBFormula.N, dbSatisfies, hρ, relInterp_canonicalStructure, modelRel]
  | pair l r =>
      constructor
      · intro hN
        exfalso
        exact h10upcSemDirect_irrefl l.1 r.1 (by
          simpa [DBFormula.N, dbSatisfies, hρ, relInterp_canonicalStructure, modelRel,
            h10upcSemDirect] using hN)
      · rintro ⟨n, hn⟩
        cases hn

theorem dbSatisfies_P'_iff
    (m : Nat) (ρ : Nat → Model m) (a : Nat) :
    dbSatisfies (canonicalStructure m) ρ (DBFormula.P' a) ↔
      ∃ l r : finNum m, ρ a = Model.pair l r := by
  cases hρ : ρ a with
  | num n =>
      constructor
      · intro hP
        have hN : dbSatisfies (canonicalStructure m) ρ (DBFormula.N a) := by
          simpa [DBFormula.N, dbSatisfies, hρ, relInterp_canonicalStructure, modelRel]
        exact False.elim (hP hN)
      · rintro ⟨l, r, hpair⟩
        cases hpair
  | pair l r =>
      constructor
      · intro _
        exact ⟨l, r, rfl⟩
      · intro _
        simp [DBFormula.P', DBFormula.neg, DBFormula.N, dbSatisfies, hρ,
          relInterp_canonicalStructure, modelRel, h10upcSemDirect_irrefl]

theorem dbSatisfies_P_iff
    (m : Nat) (ρ : Nat → Model m) (p a b : Nat) :
    dbSatisfies (canonicalStructure m) ρ (DBFormula.P p a b) ↔
      ∃ na nb : finNum m,
        ρ a = Model.num na ∧
        ρ b = Model.num nb ∧
        ρ p = Model.pair na nb := by
  constructor
  · intro hP
    rcases hP with ⟨hP', hRest⟩
    rcases (dbSatisfies_N_iff m ρ a).1 hRest.1 with ⟨na, ha⟩
    rcases (dbSatisfies_N_iff m ρ b).1 hRest.2.1 with ⟨nb, hb⟩
    rcases (dbSatisfies_P'_iff m ρ p).1 hP' with ⟨l, r, hp⟩
    have hRelAP : dbSatisfies (canonicalStructure m) ρ (DBFormula.rel a p) := hRest.2.2.1
    have hRelPB : dbSatisfies (canonicalStructure m) ρ (DBFormula.rel p b) := hRest.2.2.2
    have hlv : na.1 = l.1 := by
      simpa [dbSatisfies, relInterp_canonicalStructure, modelRel, ha, hp] using hRelAP
    have hrv : r.1 = nb.1 := by
      simpa [dbSatisfies, relInterp_canonicalStructure, modelRel, hb, hp] using hRelPB
    have hl : l = na := by
      ext
      exact hlv.symm
    have hr : r = nb := by
      ext
      exact hrv
    exact ⟨na, nb, ha, hb, hp.trans (by simpa [hl, hr])⟩
  · rintro ⟨na, nb, ha, hb, hp⟩
    simp [DBFormula.P, DBFormula.conjs, DBFormula.P', DBFormula.neg, DBFormula.N,
      dbSatisfies, relInterp_canonicalStructure, modelRel, h10upcSemDirect_irrefl,
      ha, hb, hp]

theorem dbSatisfies_deq_num_iff
    (m : Nat) (ρ : Nat → Model m) (a b : Nat)
    (na nb : finNum m)
    (ha : ρ a = Model.num na) (hb : ρ b = Model.num nb) :
    dbSatisfies (canonicalStructure m) ρ (DBFormula.deq a b) ↔ na = nb := by
  constructor
  · intro hDeq
    by_contra hne
    have hneVal : na.1 ≠ nb.1 := by
      intro hEq
      apply hne
      ext
      exact hEq
    have hAtA :
        dbSatisfies (canonicalStructure m) (consEnv (Model.pair na na) ρ)
          (DBFormula.rel 0 (a + 1)) := by
      simpa [dbSatisfies, consEnv, relInterp_canonicalStructure, modelRel, ha]
    have hNotAtB :
        ¬ dbSatisfies (canonicalStructure m) (consEnv (Model.pair na na) ρ)
          (DBFormula.rel 0 (b + 1)) := by
      simp [dbSatisfies, consEnv, relInterp_canonicalStructure, modelRel, hb, hneVal]
    have hImp :
        dbSatisfies (canonicalStructure m) (consEnv (Model.pair na na) ρ)
          (DBFormula.rel 0 (a + 1)) →
        dbSatisfies (canonicalStructure m) (consEnv (Model.pair na na) ρ)
          (DBFormula.rel 0 (b + 1)) :=
      (hDeq (Model.pair na na)).1.1
    exact hNotAtB (hImp hAtA)
  · intro hEq
    subst hEq
    intro d
    constructor
    · constructor <;> intro h <;>
        simpa [DBFormula.deq, DBFormula.iff_, dbSatisfies, consEnv,
          relInterp_canonicalStructure, modelRel, ha, hb] using h
    · constructor <;> intro h <;>
        simpa [DBFormula.deq, DBFormula.iff_, dbSatisfies, consEnv,
          relInterp_canonicalStructure, modelRel, ha, hb] using h

theorem dbSatisfies_leq_num_iff
    (m : Nat) (ρ : Nat → Model m) (a b : Nat)
    (na nb : finNum m)
    (ha : ρ a = Model.num na) (hb : ρ b = Model.num nb) :
    dbSatisfies (canonicalStructure m) ρ (DBFormula.leq a b) ↔ na.1 ≤ nb.1 := by
  simp [DBFormula.leq, DBFormula.N, DBFormula.conjs, dbSatisfies,
    relInterp_canonicalStructure, modelRel, ha, hb]

theorem dbSatisfies_less_num_iff
    (m : Nat) (ρ : Nat → Model m) (a b : Nat)
    (na nb : finNum m)
    (ha : ρ a = Model.num na) (hb : ρ b = Model.num nb) :
    dbSatisfies (canonicalStructure m) ρ (DBFormula.less a b) ↔ na.1 < nb.1 := by
  constructor
  · rintro ⟨hLe, hNotEq⟩
    have hLe' := (dbSatisfies_leq_num_iff m ρ a b na nb ha hb).1 hLe
    have hNeVal : na.1 ≠ nb.1 := by
      intro hEq
      apply hNotEq
      apply (dbSatisfies_deq_num_iff m ρ a b na nb ha hb).2
      ext
      exact hEq
    omega
  · intro hLt
    refine ⟨(dbSatisfies_leq_num_iff m ρ a b na nb ha hb).2 (Nat.le_of_lt hLt), ?_⟩
    intro hDeq
    have hEq := (dbSatisfies_deq_num_iff m ρ a b na nb ha hb).1 hDeq
    exact Nat.ne_of_lt hLt (congrArg Subtype.val hEq)

theorem dbSatisfies_relQuad_num_iff
    (m : Nat) (ρ : Nat → Model m) (a b c d : Nat)
    (na nb nc nd : finNum m)
    (ha : ρ a = Model.num na) (hb : ρ b = Model.num nb)
    (hc : ρ c = Model.num nc) (hd : ρ d = Model.num nd) :
    dbSatisfies (canonicalStructure m) ρ (DBFormula.relQuad a b c d) ↔
      h10upcSemDirect ((na.1, nb.1), (nc.1, nd.1)) := by
  constructor
  · rintro ⟨p, q, hBody⟩
    let ρ' : Nat → Model m := consEnv q (consEnv p ρ)
    have hPab := (dbSatisfies_P_iff m ρ' 1 (2 + a) (2 + b)).1 (by simpa [ρ'] using hBody.1)
    have hPcd := (dbSatisfies_P_iff m ρ' 0 (2 + c) (2 + d)).1 (by simpa [ρ'] using hBody.2.1)
    rcases hPab with ⟨na', nb', hA, hB, hP⟩
    rcases hPcd with ⟨nc', nd', hC, hD, hQ⟩
    have hna : na = na' := by
      simpa [ρ', Nat.add_comm, ha] using hA
    have hnb : nb = nb' := by
      simpa [ρ', Nat.add_comm, hb] using hB
    have hnc : nc = nc' := by
      simpa [ρ', Nat.add_comm, hc] using hC
    have hnd : nd = nd' := by
      simpa [ρ', Nat.add_comm, hd] using hD
    have hp : p = Model.pair na nb := by
      simpa [ρ', hna, hnb] using hP
    have hq : q = Model.pair nc nd := by
      simpa [ρ', hnc, hnd] using hQ
    simpa [DBFormula.relQuad, dbSatisfies, relInterp_canonicalStructure, modelRel, ρ',
      hp, hq] using hBody.2.2
  · intro hRel
    refine ⟨Model.pair na nb, Model.pair nc nd, ?_⟩
    let ρ' : Nat → Model m := consEnv (Model.pair nc nd) (consEnv (Model.pair na nb) ρ)
    have hPab :
        dbSatisfies (canonicalStructure m) ρ' (DBFormula.P 1 (2 + a) (2 + b)) := by
      refine (dbSatisfies_P_iff m ρ' 1 (2 + a) (2 + b)).2 ?_
      refine ⟨na, nb, ?_, ?_, ?_⟩
      · simpa [ρ', Nat.add_comm, ha]
      · simpa [ρ', Nat.add_comm, hb]
      · simp [ρ']
    have hPcd :
        dbSatisfies (canonicalStructure m) ρ' (DBFormula.P 0 (2 + c) (2 + d)) := by
      refine (dbSatisfies_P_iff m ρ' 0 (2 + c) (2 + d)).2 ?_
      refine ⟨nc, nd, ?_, ?_, ?_⟩
      · simpa [ρ', Nat.add_comm, hc]
      · simpa [ρ', Nat.add_comm, hd]
      · simp [ρ']
    have hPairRel :
        dbSatisfies (canonicalStructure m) ρ' (DBFormula.rel 1 0) := by
      simpa [dbSatisfies, relInterp_canonicalStructure, modelRel, ρ'] using hRel
    simpa [DBFormula.relQuad, dbSatisfies, ρ'] using ⟨hPab, hPcd, hPairRel⟩

def emplacedEnv {α : Type*} (n : Nat) (ee : Nat → α) (ρ : Nat → α) : Nat → α :=
  fun k => if hk : k < n then ee k else ρ (k - n)

@[simp] theorem emplacedEnv_lt {α : Type*}
    (n : Nat) (ee : Nat → α) (ρ : Nat → α) {k : Nat} (hk : k < n) :
    emplacedEnv n ee ρ k = ee k := by
  simp [emplacedEnv, hk]

@[simp] theorem emplacedEnv_ge {α : Type*}
    (n : Nat) (ee : Nat → α) (ρ : Nat → α) {k : Nat} (hk : n ≤ k) :
    emplacedEnv n ee ρ k = ρ (k - n) := by
  have hk' : ¬ k < n := by omega
  simp [emplacedEnv, hk', hk]

theorem emplacedEnv_succ {α : Type*} (n : Nat) (ee : Nat → α) (ρ : Nat → α) :
    emplacedEnv (n + 1) ee ρ = emplacedEnv n ee (consEnv (ee n) ρ) := by
  funext k
  by_cases hk : k < n
  · simp [emplacedEnv, hk, Nat.lt_trans hk (Nat.lt_succ_self n)]
  · have hkge : n ≤ k := Nat.le_of_not_lt hk
    cases hEq : Nat.eq_or_lt_of_le hkge with
    | inl hEq' =>
        subst hEq'
        simp [emplacedEnv, hk, Nat.lt_irrefl]
    | inr hlt =>
        have hsubpos : 0 < k - n := Nat.sub_pos_of_lt hlt
        obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsubpos)
        have hkEq : k = n + (t + 1) := by
          have := Nat.add_sub_of_le hkge
          omega
        subst hkEq
        have hsub : n + (t + 1) - (n + 1) = t := by omega
        simp [emplacedEnv, hk, hsub]

theorem dbSatisfies_emplaceExists_of
    (S : ClassicalStructure ReductionSig) (ρ : Nat → S.D) (ee : Nat → S.D) :
    ∀ n φ,
      dbSatisfies S (emplacedEnv n ee ρ) φ →
        dbSatisfies S ρ (DBFormula.emplaceExists n φ)
  | 0, φ, h => by
      simpa [DBFormula.emplaceExists, emplacedEnv] using h
  | n + 1, φ, h => by
      refine ⟨ee n, ?_⟩
      have h' : dbSatisfies S (emplacedEnv n ee (consEnv (ee n) ρ)) φ := by
        simpa [emplacedEnv_succ] using h
      simpa [DBFormula.emplaceExists] using
        dbSatisfies_emplaceExists_of S (consEnv (ee n) ρ) ee n φ h'

theorem remove_emplaceExists
    (S : ClassicalStructure ReductionSig) (ρ : Nat → S.D) :
    ∀ n φ,
      dbSatisfies S ρ (DBFormula.emplaceExists n φ) →
        ∃ ρ' : Nat → S.D, dbSatisfies S ρ' φ ∧ ∀ k, ρ k = ρ' (k + n)
  | 0, φ, h => by
      refine ⟨ρ, ?_, ?_⟩
      · simpa [DBFormula.emplaceExists] using h
      · intro k
        simp
  | n + 1, φ, h => by
      rcases h with ⟨d, hd⟩
      rcases remove_emplaceExists S (consEnv d ρ) n φ hd with ⟨ρ', hρ', hshift⟩
      refine ⟨ρ', hρ', ?_⟩
      · intro k
        have := hshift (k + 1)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

section InverseTransport

variable {S : ClassicalStructure ReductionSig}

abbrev iPr (a b : S.D) : Prop :=
  RelInterp S a b

abbrev iN (a : S.D) : Prop :=
  iPr a a

abbrev ileq (a b : S.D) : Prop :=
  iN a ∧ iN b ∧ iPr a b

abbrev iP' (a : S.D) : Prop :=
  ¬ iN a

abbrev iP (p a b : S.D) : Prop :=
  iP' p ∧ iN a ∧ iN b ∧ iPr a p ∧ iPr p b

abbrev ideq (a b : S.D) : Prop :=
  ∀ x : S.D, (iPr x a ↔ iPr x b) ∧ (iPr a x ↔ iPr b x)

abbrev iless (a b : S.D) : Prop :=
  ileq a b ∧ ¬ ideq a b

abbrev irel (a b c d : S.D) : Prop :=
  ∃ pl pr : S.D, iP pl a b ∧ iP pr c d ∧ iPr pl pr

abbrev isucc (l r z : S.D) : Prop :=
  irel l z r z

theorem to_N
    (e : Nat → S.D) (i : Nat) :
    dbSatisfies S e (DBFormula.N i) ↔ iN (e i) := by
  rfl

theorem to_leq
    (e : Nat → S.D) (a b : Nat) :
    dbSatisfies S e (DBFormula.leq a b) ↔ ileq (e a) (e b) := by
  simp [DBFormula.leq, DBFormula.N, DBFormula.conjs, iN, ileq, iPr, dbSatisfies]

theorem to_P'
    (e : Nat → S.D) (i : Nat) :
    dbSatisfies S e (DBFormula.P' i) ↔ iP' (e i) := by
  rfl

theorem to_P
    (e : Nat → S.D) (p a b : Nat) :
    dbSatisfies S e (DBFormula.P p a b) ↔ iP (e p) (e a) (e b) := by
  simp [DBFormula.P, DBFormula.P', DBFormula.neg, DBFormula.N, DBFormula.conjs,
    iP, iP', iN, iPr, dbSatisfies]

theorem to_deq
    (e : Nat → S.D) (a b : Nat) :
    dbSatisfies S e (DBFormula.deq a b) ↔ ideq (e a) (e b) := by
  constructor
  · intro h x
    rcases h x with ⟨hL, hR⟩
    exact ⟨Iff.intro hL.1 hL.2, Iff.intro hR.1 hR.2⟩
  · intro h x
    rcases h x with ⟨hL, hR⟩
    exact ⟨⟨hL.mp, hL.mpr⟩, ⟨hR.mp, hR.mpr⟩⟩

theorem to_less
    (e : Nat → S.D) (a b : Nat) :
    dbSatisfies S e (DBFormula.less a b) ↔ iless (e a) (e b) := by
  constructor
  · intro h
    refine ⟨(to_leq (S := S) e a b).1 h.1, ?_⟩
    intro hEq
    exact h.2 ((to_deq (S := S) e a b).2 hEq)
  · rintro ⟨hLe, hNe⟩
    refine ⟨(to_leq (S := S) e a b).2 hLe, ?_⟩
    intro hEq
    exact hNe ((to_deq (S := S) e a b).1 hEq)

theorem to_relQuad
    (e : Nat → S.D) (a b c d : Nat) :
    dbSatisfies S e (DBFormula.relQuad a b c d) ↔ irel (e a) (e b) (e c) (e d) := by
  constructor
  · rintro ⟨pl, pr, hBody⟩
    have hBody' := hBody
    simp [DBFormula.relQuad, DBFormula.conjs, dbSatisfies] at hBody'
    rcases hBody' with ⟨hL, hR, hRel⟩
    refine ⟨pl, pr, ?_, ?_, hRel⟩
    · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, consEnv, iP, iP', iN, iPr] using
        (to_P (S := S) (e := consEnv pr (consEnv pl e)) 1 (2 + a) (2 + b)).1 hL
    · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, consEnv, iP, iP', iN, iPr] using
        (to_P (S := S) (e := consEnv pr (consEnv pl e)) 0 (2 + c) (2 + d)).1 hR
  · rintro ⟨pl, pr, hBody⟩
    rcases hBody with ⟨hL, hR, hRel⟩
    refine ⟨pl, pr, ?_⟩
    have hL' :
        dbSatisfies S (consEnv pr (consEnv pl e)) (DBFormula.P 1 (2 + a) (2 + b)) := by
      exact (to_P (S := S) (e := consEnv pr (consEnv pl e)) 1 (2 + a) (2 + b)).2 <|
        by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, consEnv, iP, iP', iN, iPr] using hL
    have hR' :
        dbSatisfies S (consEnv pr (consEnv pl e)) (DBFormula.P 0 (2 + c) (2 + d)) := by
      exact (to_P (S := S) (e := consEnv pr (consEnv pl e)) 0 (2 + c) (2 + d)).2 <|
        by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, consEnv, iP, iP', iN, iPr] using hR
    simpa [DBFormula.relQuad, DBFormula.conjs, dbSatisfies] using ⟨hL', hR', hRel⟩

theorem to_succ
    (e : Nat → S.D) (a b z : Nat) :
    dbSatisfies S e (DBFormula.succ a b z) ↔ isucc (e a) (e b) (e z) := by
  simpa [DBFormula.succ, isucc] using to_relQuad (S := S) e a z b z

theorem dEqRefl (d : S.D) : ideq d d := by
  intro x
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem dEqSymm {d1 d2 : S.D} : ideq d1 d2 → ideq d2 d1 := by
  intro h x
  rcases h x with ⟨hL, hR⟩
  exact ⟨hL.symm, hR.symm⟩

theorem dEqTrans {d1 d2 d3 : S.D} :
    ideq d1 d2 → ideq d2 d3 → ideq d1 d3 := by
  intro h12 h23 x
  rcases h12 x with ⟨h12L, h12R⟩
  rcases h23 x with ⟨h23L, h23R⟩
  exact ⟨h12L.trans h23L, h12R.trans h23R⟩

theorem iPr_congr {a b a' b' : S.D}
    (hA : ideq a a') (hB : ideq b b') :
    iPr a b ↔ iPr a' b' := by
  constructor
  · intro h
    have ha' : iPr a' b := ((hA b).2).1 h
    exact ((hB a').1).1 ha'
  · intro h
    have ha' : iPr a' b := ((hB a').1).2 h
    exact ((hA b).2).2 ha'

theorem iN_congr {a b : S.D} (h : ideq a b) : iN a ↔ iN b := by
  simpa [iN] using iPr_congr (S := S) h h

theorem ileq_congr {a b a' b' : S.D}
    (hA : ideq a a') (hB : ideq b b') :
    ileq a b ↔ ileq a' b' := by
  simp [ileq, iN_congr (S := S) hA, iN_congr (S := S) hB, iPr_congr (S := S) hA hB]

theorem iless_congr {a b a' b' : S.D}
    (hA : ideq a a') (hB : ideq b b') :
    iless a b ↔ iless a' b' := by
  constructor
  · rintro ⟨hLe, hNe⟩
    refine ⟨(ileq_congr (S := S) hA hB).1 hLe, ?_⟩
    intro hEq
    apply hNe
    exact dEqTrans (S := S) hA (dEqTrans (S := S) hEq (dEqSymm (S := S) hB))
  · rintro ⟨hLe, hNe⟩
    refine ⟨(ileq_congr (S := S) hA hB).2 hLe, ?_⟩
    intro hEq
    apply hNe
    exact dEqTrans (S := S) (dEqSymm (S := S) hA) (dEqTrans (S := S) hEq hB)

theorem iP_congr {p a b p' a' b' : S.D}
    (hP : ideq p p') (hA : ideq a a') (hB : ideq b b') :
    iP p a b ↔ iP p' a' b' := by
  constructor
  · rintro ⟨hP', hNa, hNb, hAP, hPB⟩
    exact ⟨fun h => hP' ((iN_congr (S := S) hP).2 h),
      (iN_congr (S := S) hA).1 hNa,
      (iN_congr (S := S) hB).1 hNb,
      (iPr_congr (S := S) hA hP).1 hAP,
      (iPr_congr (S := S) hP hB).1 hPB⟩
  · rintro ⟨hP', hNa, hNb, hAP, hPB⟩
    exact ⟨fun h => hP' ((iN_congr (S := S) hP).1 h),
      (iN_congr (S := S) hA).2 hNa,
      (iN_congr (S := S) hB).2 hNb,
      (iPr_congr (S := S) hA hP).2 hAP,
      (iPr_congr (S := S) hP hB).2 hPB⟩

theorem irel_congr {a b c d a' b' c' d' : S.D}
    (hA : ideq a a') (hB : ideq b b') (hC : ideq c c') (hD : ideq d d') :
    irel a b c d ↔ irel a' b' c' d' := by
  constructor
  · rintro ⟨pl, pr, hL, hR, hRel⟩
    exact ⟨pl, pr,
      (iP_congr (S := S) (dEqRefl (S := S) pl) hA hB).mp hL,
      (iP_congr (S := S) (dEqRefl (S := S) pr) hC hD).mp hR,
      (iPr_congr (S := S) (dEqRefl (S := S) pl) (dEqRefl (S := S) pr)).mp hRel⟩
  · rintro ⟨pl, pr, hL, hR, hRel⟩
    exact ⟨pl, pr,
      (iP_congr (S := S) (dEqRefl (S := S) pl) hA hB).mpr hL,
      (iP_congr (S := S) (dEqRefl (S := S) pr) hC hD).mpr hR,
      (iPr_congr (S := S) (dEqRefl (S := S) pl) (dEqRefl (S := S) pr)).mpr hRel⟩

theorem isucc_congr {l r z l' r' z' : S.D}
    (hL : ideq l l') (hR : ideq r r') (hZ : ideq z z') :
    isucc l r z ↔ isucc l' r' z' := by
  simpa [isucc] using irel_congr (S := S) hL hZ hR hZ

theorem leq_eq {a b : S.D} :
    iN b → ideq a b → ileq a b := by
  intro hNb hEq
  have hNa : iN a := (iN_congr (S := S) hEq).2 hNb
  have hRel : iPr a b := by
    have hbb : iPr b b := hNb
    exact (iPr_congr (S := S) hEq (dEqRefl (S := S) b)).2 hbb
  exact ⟨hNa, hNb, hRel⟩

section WithAxioms

variable [Finite S.D]
variable {ρ : Nat → S.D} {m z : S.D}
variable
  (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans)
  (vPred : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aPred 1))
  (vSucc : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aSucc 1))

theorem vpTrans {a b c : S.D}
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans) :
    iless a b → iless b c → iless a c := by
  intro hAB hBC
  let e : Nat → S.D := consEnv c (consEnv b (consEnv a (consEnv m (consEnv z ρ))))
  have h21 : dbSatisfies S e (DBFormula.less 2 1) := by
    exact (to_less (S := S) (e := e) 2 1).2 <| by
      simpa [e, consEnv] using hAB
  have h10 : dbSatisfies S e (DBFormula.less 1 0) := by
    exact (to_less (S := S) (e := e) 1 0).2 <| by
      simpa [e, consEnv] using hBC
  have h20 : dbSatisfies S e (DBFormula.less 2 0) := vTrans a b c h21 h10
  exact (to_less (S := S) (e := e) 2 0).1 <| by
    simpa [e, consEnv] using h20

theorem vpPred {x : S.D}
    (vPred : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aPred 1)) :
    iN x → ¬ ideq x z → ∃ p : S.D, isucc p x z := by
  intro hNx hNot
  let e : Nat → S.D := consEnv x (consEnv m (consEnv z ρ))
  have hN0 : dbSatisfies S e (DBFormula.N 0) := by
    exact (to_N (S := S) e 0).2 <| by
      simpa [e, consEnv] using hNx
  have hNotDeq : dbSatisfies S e (DBFormula.neg (DBFormula.deq 2 0)) := by
    intro hDeq
    apply hNot
    exact dEqSymm (S := S) <| (to_deq (S := S) e 2 0).1 hDeq
  rcases vPred x hN0 hNotDeq with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  exact (to_succ (S := S) (e := consEnv p e) 0 1 3).1 <| by
    simpa [e, consEnv] using hp

theorem vpSucc {l r : S.D}
    (vSucc : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aSucc 1)) :
    isucc l r z → iless l r ∧ ∀ k : S.D, iless k r → ileq k l := by
  intro hSucc
  rcases hSucc with ⟨pl, pr, hPl, hPr, hRel⟩
  have hSucc' : isucc l r z := ⟨pl, pr, hPl, hPr, hRel⟩
  have hNl : iN l := hPl.2.1
  have hNr : iN r := hPr.2.1
  let e : Nat → S.D := consEnv r (consEnv l (consEnv m (consEnv z ρ)))
  have hN1 : dbSatisfies S e (DBFormula.N 1) := by
    exact (to_N (S := S) e 1).2 <| by
      simpa [e, consEnv] using hNl
  have hN0 : dbSatisfies S e (DBFormula.N 0) := by
    exact (to_N (S := S) e 0).2 <| by
      simpa [e, consEnv] using hNr
  have hRelDb : dbSatisfies S e (DBFormula.relQuad 1 3 0 3) := by
    exact (to_relQuad (S := S) e 1 3 0 3).2 <| by
      simpa [e, consEnv, isucc] using hSucc'
  have hMain := vSucc l r hN1 hN0 hRelDb
  refine ⟨(to_less (S := S) (e := e) 1 0).1 <| by simpa [e, consEnv] using hMain.1, ?_⟩
  intro k hKr
  have hkDb : dbSatisfies S (consEnv k e) (DBFormula.less 0 1) := by
    exact (to_less (S := S) (e := consEnv k e) 0 1).2 <| by
      simpa [e, consEnv] using hKr
  have hkLe : dbSatisfies S (consEnv k e) (DBFormula.leq 0 2) := hMain.2 k hkDb
  exact (to_leq (S := S) (e := consEnv k e) 0 2).1 <| by
    simpa [e, consEnv] using hkLe

theorem less_irref {x : S.D} : ¬ iless x x := by
  intro h
  exact h.2 (dEqRefl (S := S) x)

theorem less_wf
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans) :
    WellFounded (fun a b : S.D => iless a b) := by
  letI : IsTrans S.D (fun a b : S.D => iless a b) :=
    ⟨fun a b c hab hbc => vpTrans (S := S) (ρ := ρ) (m := m) (z := z) vTrans hab hbc⟩
  letI : IsIrrefl S.D (fun a b : S.D => iless a b) := ⟨fun a => less_irref (S := S)⟩
  exact Finite.wellFounded_of_trans_of_irrefl (fun a b : S.D => iless a b)

theorem less_leq {a b c : S.D} :
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans) →
    iless a b → ileq b c → iless a c := by
  intro vTrans hAB hBC
  by_cases hEq : ideq b c
  · exact (iless_congr (S := S) (dEqRefl (S := S) a) hEq).1 hAB
  · exact vpTrans (S := S) (ρ := ρ) (m := m) (z := z) vTrans hAB ⟨hBC, hEq⟩

theorem leq_less {a b c : S.D} :
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans) →
    ileq a b → iless b c → iless a c := by
  intro vTrans hAB hBC
  by_cases hEq : ideq a b
  · exact (iless_congr (S := S) hEq (dEqRefl (S := S) c)).2 hBC
  · exact vpTrans (S := S) (ρ := ρ) (m := m) (z := z) vTrans ⟨hAB, hEq⟩ hBC

theorem leq_trans {a b c : S.D} :
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans) →
    ileq a b → ileq b c → ileq a c := by
  intro vTrans hAB hBC
  by_cases hEq : ideq a b
  · exact (ileq_congr (S := S) hEq (dEqRefl (S := S) c)).2 hBC
  · by_cases hEq' : ideq b c
    · exact (ileq_congr (S := S) (dEqRefl (S := S) a) hEq').1 hAB
    · exact (vpTrans (S := S) (ρ := ρ) (m := m) (z := z) vTrans ⟨hAB, hEq⟩ ⟨hBC, hEq'⟩).1

theorem aZeroS {k : S.D} :
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans) →
    (vPred : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aPred 1)) →
    (vSucc : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aSucc 1)) →
    ¬ iless k z := by
  intro vTrans vPred vSucc
  let P : S.D → Prop := fun x => ¬ iless x z
  have hStep : ∀ x : S.D, (∀ y : S.D, iless y x → P y) → P x := by
    intro x IH hxz
    have hxN : iN x := hxz.1.1
    have hxNot : ¬ ideq x z := hxz.2
    rcases vpPred (S := S) (ρ := ρ) (m := m) (z := z) vPred hxN hxNot with ⟨p, hp⟩
    have hpData := vpSucc (S := S) (ρ := ρ) (m := m) (z := z) vSucc hp
    exact IH p hpData.1 <|
      less_leq (S := S) (ρ := ρ) (m := m) (z := z) vTrans hpData.1 hxz.1
  exact (less_wf (S := S) (ρ := ρ) (m := m) (z := z) vTrans).induction k hStep

theorem aZero2 {k : S.D} :
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans) →
    (vPred : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aPred 1)) →
    (vSucc : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aSucc 1)) →
    iN k → ileq z k := by
  intro vTrans vPred vSucc
  let P : S.D → Prop := fun x => iN x → ileq z x
  have hStep : ∀ x : S.D, (∀ y : S.D, iless y x → P y) → P x := by
    intro x IH hxN
    by_cases hEq : ideq z x
    · exact leq_eq (S := S) hxN hEq
    · have hxNot : ¬ ideq x z := by
        intro hxz
        exact hEq (dEqSymm (S := S) hxz)
      rcases vpPred (S := S) (ρ := ρ) (m := m) (z := z) vPred hxN hxNot with ⟨p, hp⟩
      have hpData := vpSucc (S := S) (ρ := ρ) (m := m) (z := z) vSucc hp
      have hzp : ileq z p := IH p hpData.1 hpData.1.1.1
      exact (leq_less (S := S) (ρ := ρ) (m := m) (z := z) vTrans hzp hpData.1).1
  exact (less_wf (S := S) (ρ := ρ) (m := m) (z := z) vTrans).induction k hStep

theorem antiSym {a b : S.D} :
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans) →
    ileq a b → ileq b a → ideq a b := by
  intro vTrans hAB hBA
  by_cases hEq : ideq a b
  · exact hEq
  · have hBA' : iless b a := by
      refine ⟨hBA, ?_⟩
      intro hba
      exact hEq (dEqSymm (S := S) hba)
    have hAA := leq_less (S := S) (ρ := ρ) (m := m) (z := z) vTrans hAB hBA'
    exact False.elim (less_irref (S := S) hAA)

def chain (z m : S.D) (mN : Nat) (f : S.D → Option Nat) : Prop :=
  (∀ d, ileq d m ↔ f d ≠ none) ∧
  (∀ n, (∃ d, ileq d m ∧ f d = some n) → n ≤ mN) ∧
  f m = some mN ∧
  f z = some 0 ∧
  (∀ dl dh l h, f dl = some l → f dh = some h → (Nat.succ l = h ↔ isucc dl dh z)) ∧
  (∀ d1 d2, f d1 ≠ none → (f d1 = f d2 ↔ ideq d1 d2))

theorem mkchain_zero
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans)
    (vPred : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aPred 1))
    (vSucc : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aSucc 1))
    {dd : S.D} (hN : iN dd) (hdz : ideq dd z) :
    ∃ n f, chain z dd n f := by
  classical
  let f : S.D → Option Nat := fun k => if ideq k dd then some 0 else none
  have hDomain : ∀ d, ileq d dd ↔ f d ≠ none := by
    intro d
    constructor
    · intro hdle
      by_cases hEq : ideq d dd
      · simp [f, hEq]
      · have hdlt : iless d dd := ⟨hdle, hEq⟩
        have hdzlt : iless d z :=
          (iless_congr (S := S) (dEqRefl (S := S) d) hdz).1 hdlt
        exact False.elim <| aZeroS (S := S) (ρ := ρ) (m := m) (z := z) vTrans vPred vSucc hdzlt
    · intro hNotNone
      by_cases hEq : ideq d dd
      · exact leq_eq (S := S) hN hEq
      · simp [f, hEq] at hNotNone
  have hBound : ∀ n, (∃ d, ileq d dd ∧ f d = some n) → n ≤ 0 := by
    intro n hn
    rcases hn with ⟨d, hdle, hfd⟩
    by_cases hEq : ideq d dd
    · have hn0 : n = 0 := by
        rw [show f d = ite (ideq d dd) (some 0) none by rfl, if_pos hEq] at hfd
        exact Option.some.inj hfd.symm
      omega
    · have hdlt : iless d dd := ⟨hdle, hEq⟩
      have hdzlt : iless d z :=
          (iless_congr (S := S) (dEqRefl (S := S) d) hdz).1 hdlt
      exact False.elim <| aZeroS (S := S) (ρ := ρ) (m := m) (z := z) vTrans vPred vSucc hdzlt
  have hSelf : f dd = some 0 := by
    simp [f, dEqRefl (S := S) dd]
  have hZero : f z = some 0 := by
    simp [f, dEqSymm (S := S) hdz]
  have hSuccStep :
      ∀ dl dh l h, f dl = some l → f dh = some h → (Nat.succ l = h ↔ isucc dl dh z) := by
    intro dl dh l h hdl hdh
    by_cases hdlEq : ideq dl dd
    · by_cases hdhEq : ideq dh dd
      · have hl0 : l = 0 := by
          rw [show f dl = ite (ideq dl dd) (some 0) none by rfl, if_pos hdlEq] at hdl
          exact Option.some.inj hdl.symm
        have hh0 : h = 0 := by
          rw [show f dh = ite (ideq dh dd) (some 0) none by rfl, if_pos hdhEq] at hdh
          exact Option.some.inj hdh.symm
        subst hl0
        subst hh0
        constructor
        · intro hImpossible
          omega
        · intro hSucc
          have hdhz : ideq dh z := dEqTrans (S := S) hdhEq hdz
          have hdltz : iless dl z := by
            have hdlt : iless dl dh :=
              (vpSucc (S := S) (ρ := ρ) (m := m) (z := z) vSucc hSucc).1
            exact (iless_congr (S := S) (dEqRefl (S := S) dl) hdhz).1 hdlt
          exact False.elim <| aZeroS (S := S) (ρ := ρ) (m := m) (z := z) vTrans vPred vSucc hdltz
      · simp [f, hdhEq] at hdh
    · simp [f, hdlEq] at hdl
  have hEqClass :
      ∀ d1 d2, f d1 ≠ none → (f d1 = f d2 ↔ ideq d1 d2) := by
    intro d1 d2 hd1
    have hd1Eq : ideq d1 dd := by
      by_cases hEq : ideq d1 dd
      · exact hEq
      · simp [f, hEq] at hd1
    constructor
    · intro hfd
      by_cases hEq : ideq d2 dd
      · exact dEqTrans (S := S) hd1Eq (dEqSymm (S := S) hEq)
      · have : f d2 = none := by simp [f, hEq]
        have hd1none : f d1 = none := hfd.trans this
        exact False.elim (hd1 hd1none)
    · intro hd12
      have hd2Eq : ideq d2 dd := dEqTrans (S := S) (dEqSymm (S := S) hd12) hd1Eq
      rw [show f d1 = ite (ideq d1 dd) (some 0) none by rfl, if_pos hd1Eq]
      rw [show f d2 = ite (ideq d2 dd) (some 0) none by rfl, if_pos hd2Eq]
  exact ⟨0, f, hDomain, hBound, hSelf, hZero, hSuccStep, hEqClass⟩

theorem mkchain
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans)
    (vPred : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aPred 1))
    (vSucc : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aSucc 1))
    {dd : S.D} (hN : iN dd) :
    ∃ n f, chain z dd n f := by
  classical
  let P : S.D → Prop := fun d => iN d → ∃ n f, chain z d n f
  have hStep : ∀ d : S.D, (∀ p : S.D, iless p d → P p) → P d := by
    intro d IH hNd
    by_cases hdz : ideq d z
    · exact mkchain_zero (S := S) (ρ := ρ) (m := m) (z := z) vTrans vPred vSucc hNd hdz
    · rcases vpPred (S := S) (ρ := ρ) (m := m) (z := z) vPred hNd hdz with ⟨p, hp⟩
      have hpData := vpSucc (S := S) (ρ := ρ) (m := m) (z := z) vSucc hp
      rcases IH p hpData.1 hpData.1.1.1 with ⟨n, f, hf⟩
      rcases hf with ⟨hDom, hBound, hTop, hZero, hSuccStep, hEqClass⟩
      let g : S.D → Option Nat := fun v => if ideq v d then some (Nat.succ n) else f v
      refine ⟨Nat.succ n, g, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x
        constructor
        · intro hxd
          by_cases hEq : ideq x d
          · intro hNone
            have hs : g x = none := hNone
            rw [show g x = ite (ideq x d) (some (Nat.succ n)) (f x) by rfl, if_pos hEq] at hs
            cases hs
          · have hxlt : iless x d := ⟨hxd, hEq⟩
            have hxp : ileq x p := hpData.2 x hxlt
            have hxSome : f x ≠ none := (hDom x).1 hxp
            simp [g, hEq, hxSome]
        · intro hxSome
          by_cases hEq : ideq x d
          · exact leq_eq (S := S) hNd hEq
          · have hxSome' : f x ≠ none := by
              simpa [g, hEq] using hxSome
            have hxp : ileq x p := (hDom x).2 hxSome'
            exact leq_trans (S := S) (ρ := ρ) (m := m) (z := z) vTrans hxp hpData.1.1
      · intro n0 hn0
        rcases hn0 with ⟨x, hxd, hxVal⟩
        by_cases hEq : ideq x d
        · have hnEq : Nat.succ n = n0 := by
            rw [show g x = ite (ideq x d) (some (Nat.succ n)) (f x) by rfl, if_pos hEq] at hxVal
            exact Option.some.inj hxVal
          omega
        · have hxVal' : f x = some n0 := by
            simpa [g, hEq] using hxVal
          have hxp : ileq x p := hpData.2 x ⟨hxd, hEq⟩
          have hnLe : n0 ≤ n := hBound n0 ⟨x, hxp, hxVal'⟩
          omega
      · simp [g, dEqRefl (S := S) d]
      · by_cases hEq : ideq z d
        · exfalso
          exact hdz (dEqSymm (S := S) hEq)
        · simpa [g, hEq] using hZero
      · intro dl dh l h hdl hdh
        constructor
        · intro hSuccNum
          by_cases hdlEq : ideq dl d
          · by_cases hdhEq : ideq dh d
            · have hlEq : l = Nat.succ n := by
                rw [show g dl = ite (ideq dl d) (some (Nat.succ n)) (f dl) by rfl, if_pos hdlEq] at hdl
                exact Option.some.inj hdl.symm
              have hhEq : h = Nat.succ n := by
                rw [show g dh = ite (ideq dh d) (some (Nat.succ n)) (f dh) by rfl, if_pos hdhEq] at hdh
                exact Option.some.inj hdh.symm
              subst hlEq
              subst hhEq
              exfalso
              omega
            · exfalso
              have hlEq : l = Nat.succ n := by
                rw [show g dl = ite (ideq dl d) (some (Nat.succ n)) (f dl) by rfl, if_pos hdlEq] at hdl
                exact Option.some.inj hdl.symm
              have hdh' : f dh = some h := by
                simpa [g, hdhEq] using hdh
              have hdhSome : f dh ≠ none := by
                intro hNone
                rw [hNone] at hdh'
                cases hdh'
              have hdhDom : ileq dh p := (hDom dh).2 hdhSome
              have hhEq : h = Nat.succ (Nat.succ n) := by
                omega
              have hdh'' : f dh = some (Nat.succ (Nat.succ n)) := by
                simpa [hhEq] using hdh'
              have hhLe' : Nat.succ (Nat.succ n) ≤ n := by
                exact hBound (Nat.succ (Nat.succ n)) ⟨dh, hdhDom, hdh''⟩
              omega
          · by_cases hdhEq : ideq dh d
            · have hdl' : f dl = some l := by
                rw [show g dl = ite (ideq dl d) (some (Nat.succ n)) (f dl) by rfl, if_neg hdlEq] at hdl
                exact hdl
              have hhEq : h = Nat.succ n := by
                rw [show g dh = ite (ideq dh d) (some (Nat.succ n)) (f dh) by rfl, if_pos hdhEq] at hdh
                exact Option.some.inj hdh.symm
              have hlEq : l = n := by
                omega
              have hdlp : ideq dl p := by
                have hdlSome : f dl ≠ none := by
                  intro hNone
                  rw [hNone] at hdl'
                  cases hdl'
                exact (hEqClass dl p hdlSome).1 <| by
                  calc
                    f dl = some l := hdl'
                    _ = some n := by simpa [hlEq]
                    _ = f p := hTop.symm
              exact (isucc_congr (S := S) hdlp hdhEq (dEqRefl (S := S) z)).2 hp
            · have hdl' : f dl = some l := by
                simpa [g, hdlEq] using hdl
              have hdh' : f dh = some h := by
                simpa [g, hdhEq] using hdh
              exact (hSuccStep dl dh l h hdl' hdh').1 hSuccNum
        · intro hSucc
          by_cases hdlEq : ideq dl d
          · by_cases hdhEq : ideq dh d
            · exfalso
              have hdlt : iless dl dh := (vpSucc (S := S) (ρ := ρ) (m := m) (z := z) vSucc hSucc).1
              exact hdlt.2 (dEqTrans (S := S) hdlEq (dEqSymm (S := S) hdhEq))
            · exfalso
              have hdlt : iless dl dh := (vpSucc (S := S) (ρ := ρ) (m := m) (z := z) vSucc hSucc).1
              have hddh : iless d dh := by
                exact (iless_congr (S := S) hdlEq (dEqRefl (S := S) dh)).1 hdlt
              have hdh' : f dh = some h := by
                simpa [g, hdhEq] using hdh
              have hdhSome : f dh ≠ none := by
                intro hNone
                rw [hNone] at hdh'
                cases hdh'
              have hdhp : ileq dh p := (hDom dh).2 hdhSome
              have hdhd : iless dh d :=
                leq_less (S := S) (ρ := ρ) (m := m) (z := z) vTrans hdhp hpData.1
              exact less_irref (S := S) (vpTrans (S := S) (ρ := ρ) (m := m) (z := z) vTrans hddh hdhd)
          · by_cases hdhEq : ideq dh d
            · have hdlp : ideq dl p := by
                have hSuccData := vpSucc (S := S) (ρ := ρ) (m := m) (z := z) vSucc hSucc
                apply antiSym (S := S) (ρ := ρ) (m := m) (z := z) vTrans
                · exact hpData.2 dl ((iless_congr (S := S) (dEqRefl (S := S) dl) hdhEq).1 hSuccData.1)
                · exact hSuccData.2 p ((iless_congr (S := S) (dEqRefl (S := S) p) hdhEq).2 hpData.1)
              have hdl' : f dl = some l := by
                simpa [g, hdlEq] using hdl
              have hdlSome : f dl ≠ none := by
                intro hNone
                rw [hNone] at hdl'
                cases hdl'
              have hfp : f dl = f p := (hEqClass dl p hdlSome).2 hdlp
              have hlEq : l = n := by
                exact Option.some.inj <| by
                  calc
                    some l = f dl := hdl'.symm
                    _ = f p := hfp
                    _ = some n := hTop
              have hhEq : h = Nat.succ n := by
                rw [show g dh = ite (ideq dh d) (some (Nat.succ n)) (f dh) by rfl, if_pos hdhEq] at hdh
                exact Option.some.inj hdh.symm
              omega
            · have hdl' : f dl = some l := by
                simpa [g, hdlEq] using hdl
              have hdh' : f dh = some h := by
                simpa [g, hdhEq] using hdh
              exact (hSuccStep dl dh l h hdl' hdh').2 hSucc
      · intro d1 d2 hd1
        constructor
        · intro hEq
          by_cases hd1Eq : ideq d1 d
          · by_cases hd2Eq : ideq d2 d
            · exact dEqTrans (S := S) hd1Eq (dEqSymm (S := S) hd2Eq)
            · exfalso
              have hd2Le : n + 1 ≤ n := by
                have hd2Val : f d2 = some (Nat.succ n) := by
                  rw [show g d1 = ite (ideq d1 d) (some (Nat.succ n)) (f d1) by rfl, if_pos hd1Eq] at hEq
                  rw [show g d2 = ite (ideq d2 d) (some (Nat.succ n)) (f d2) by rfl, if_neg hd2Eq] at hEq
                  simpa using hEq.symm
                have hd2Some : f d2 ≠ none := by
                  intro hNone
                  rw [hNone] at hd2Val
                  cases hd2Val
                have hd2Dom : ileq d2 p := (hDom d2).2 hd2Some
                exact hBound (Nat.succ n) ⟨d2, hd2Dom, hd2Val⟩
              omega
          · by_cases hd2Eq : ideq d2 d
            · exfalso
              have hd1Val : f d1 = some (Nat.succ n) := by
                rw [show g d1 = ite (ideq d1 d) (some (Nat.succ n)) (f d1) by rfl, if_neg hd1Eq] at hEq
                rw [show g d2 = ite (ideq d2 d) (some (Nat.succ n)) (f d2) by rfl, if_pos hd2Eq] at hEq
                simpa using hEq
              have hd1Dom : ileq d1 p := (hDom d1).2 (by
                intro hNone
                rw [hNone] at hd1Val
                cases hd1Val)
              have hd1Le : n + 1 ≤ n := hBound (Nat.succ n) ⟨d1, hd1Dom, hd1Val⟩
              omega
            · exact (hEqClass d1 d2 (by simpa [g, hd1Eq] using hd1)).1 (by simpa [g, hd1Eq, hd2Eq] using hEq)
        · intro hEq
          by_cases hd1Eq : ideq d1 d
          · have hd2Eq : ideq d2 d := dEqTrans (S := S) (dEqSymm (S := S) hEq) hd1Eq
            rw [show g d1 = ite (ideq d1 d) (some (Nat.succ n)) (f d1) by rfl]
            rw [show g d2 = ite (ideq d2 d) (some (Nat.succ n)) (f d2) by rfl]
            rw [if_pos hd1Eq, if_pos hd2Eq]
          · have hd2Eq : ¬ ideq d2 d := by
              intro hd2d
              exact hd1Eq (dEqTrans (S := S) hEq hd2d)
            have hd1' : f d1 ≠ none := by
              simpa [g, hd1Eq] using hd1
            have hff : f d1 = f d2 := (hEqClass d1 d2 hd1').2 hEq
            simpa [g, hd1Eq, hd2Eq] using hff
  exact (less_wf (S := S) (ρ := ρ) (m := m) (z := z) vTrans).induction dd hStep hN

def chainEnv (f : S.D → Option Nat) : S.D → Nat
  | d =>
      match f d with
      | some n => n
      | none => 0

theorem chain_proves
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans)
    (vSucc : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aSucc 1))
    (vDescr : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aDescr 1))
    (vDescr2 : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aDescr2 1))
    {a b c d₀ : S.D} {nm : Nat} {f : S.D → Option Nat}
    (hChain : chain z m nm f)
    (hbm : ileq b m) (habcd : irel a b c d₀)
    (ham : ileq a m) (hcm : ileq c m) (hdm : ileq d₀ m) :
    ∃ a' b' c' d',
      h10upcSemDirect ((a', b'), (c', d')) ∧
      f a = some a' ∧
      f b = some b' ∧
      f c = some c' ∧
      f d₀ = some d' := by
  classical
  let Q : S.D → Prop :=
    fun b =>
      ∀ a c d₀ nm (f : S.D → Option Nat),
        chain z m nm f → ileq b m → irel a b c d₀ →
        ileq a m → ileq c m → ileq d₀ m →
        ∃ a' b' c' d',
          h10upcSemDirect ((a', b'), (c', d')) ∧
          f a = some a' ∧
          f b = some b' ∧
          f c = some c' ∧
          f d₀ = some d'
  have hMain : Q b := (less_wf (S := S) (ρ := ρ) (m := m) (z := z) vTrans).induction b ?_
  exact hMain a c d₀ nm f hChain hbm habcd ham hcm hdm
  intro b IH a c d₀ nm f hChain hbm habcd ham hcm hdm
  rcases hChain with ⟨hDom, hBound, hTop, hZero, hSuccStep, hEqClass⟩
  have hChain' : chain z m nm f := ⟨hDom, hBound, hTop, hZero, hSuccStep, hEqClass⟩
  by_cases hbz : ideq b z
  · let e : Nat → S.D := consEnv d₀ (consEnv c (consEnv b (consEnv a (consEnv m (consEnv z ρ)))))
    have hNa : dbSatisfies S e (DBFormula.N 3) := by
      exact (to_N (S := S) e 3).2 <| by simpa [e, consEnv] using ham.1
    have hNb : dbSatisfies S e (DBFormula.N 2) := by
      exact (to_N (S := S) e 2).2 <| by simpa [e, consEnv] using hbm.1
    have hNc : dbSatisfies S e (DBFormula.N 1) := by
      exact (to_N (S := S) e 1).2 <| by simpa [e, consEnv] using hcm.1
    have hNd : dbSatisfies S e (DBFormula.N 0) := by
      exact (to_N (S := S) e 0).2 <| by simpa [e, consEnv] using hdm.1
    have hRel : dbSatisfies S e (DBFormula.relQuad 3 2 1 0) := by
      exact (to_relQuad (S := S) e 3 2 1 0).2 <| by simpa [e, consEnv] using habcd
    have hDeqB : dbSatisfies S e (DBFormula.deq 2 5) := by
      exact (to_deq (S := S) e 2 5).2 <| by simpa [e, consEnv] using hbz
    have hDeqDdb : dbSatisfies S e (DBFormula.deq 0 5) := vDescr2 a b c d₀ hNa hNb hNc hNd hRel hDeqB
    have hdz : ideq d₀ z := by
      exact (to_deq (S := S) e 0 5).1 <| by simpa [e, consEnv] using hDeqDdb
    cases hfa : f a with
    | none =>
        exfalso
        exact (hDom a).1 ham hfa
    | some na =>
        cases hfc : f c with
        | none =>
            exfalso
            exact (hDom c).1 hcm hfc
        | some sc =>
            have hfb : f b = some 0 := by
              have hbSome : f b ≠ none := (hDom b).1 hbm
              have hEq : f b = f z := (hEqClass b z hbSome).2 hbz
              calc
                f b = f z := hEq
                _ = some 0 := hZero
            have hfd : f d₀ = some 0 := by
              have hdSome : f d₀ ≠ none := (hDom d₀).1 hdm
              have hEq : f d₀ = f z := (hEqClass d₀ z hdSome).2 hdz
              calc
                f d₀ = f z := hEq
                _ = some 0 := hZero
            have hSucc : isucc a c z := by
              simpa [isucc] using
                (irel_congr (S := S)
                  (dEqRefl (S := S) a) hbz
                  (dEqRefl (S := S) c) hdz).1 habcd
            have hsc : Nat.succ na = sc := (hSuccStep a c na sc hfa hfc).2 hSucc
            refine ⟨na, 0, sc, 0, ?_⟩
            constructor
            · constructor <;> omega
            · constructor
              · rfl
              · constructor
                · exact hfb
                · constructor
                  · rfl
                  · exact hfd
  · let e : Nat → S.D := consEnv d₀ (consEnv c (consEnv b (consEnv a (consEnv m (consEnv z ρ)))))
    have hNa : dbSatisfies S e (DBFormula.N 3) := by
      exact (to_N (S := S) e 3).2 <| by simpa [e, consEnv] using ham.1
    have hNb : dbSatisfies S e (DBFormula.N 2) := by
      exact (to_N (S := S) e 2).2 <| by simpa [e, consEnv] using hbm.1
    have hNc : dbSatisfies S e (DBFormula.N 1) := by
      exact (to_N (S := S) e 1).2 <| by simpa [e, consEnv] using hcm.1
    have hNd : dbSatisfies S e (DBFormula.N 0) := by
      exact (to_N (S := S) e 0).2 <| by simpa [e, consEnv] using hdm.1
    have hRel : dbSatisfies S e (DBFormula.relQuad 3 2 1 0) := by
      exact (to_relQuad (S := S) e 3 2 1 0).2 <| by simpa [e, consEnv] using habcd
    have hNotDeq : dbSatisfies S e (DBFormula.neg (DBFormula.deq 5 2)) := by
      intro hDeq
      apply hbz
      exact dEqSymm (S := S) ((to_deq (S := S) e 5 2).1 hDeq)
    rcases vDescr a b c d₀ hNa hNb hNc hNd hNotDeq hRel with ⟨b', hbBody⟩
    rcases hbBody with ⟨c', hcBody⟩
    rcases hcBody with ⟨d', hBody⟩
    let e' : Nat → S.D := consEnv d' (consEnv c' (consEnv b' e))
    rcases hBody with ⟨hBsuccDb, hRest⟩
    rcases hRest with ⟨hCsuccDb, hRest⟩
    rcases hRest with ⟨hRel1Db, hRest⟩
    rcases hRest with ⟨hRel2Db, hLessDb⟩
    have hBsucc : isucc b' b z := by
      exact (to_succ (S := S) e' 2 5 8).1 <| by
        simpa [e', e, consEnv] using hBsuccDb
    have hCsucc : isucc c' c z := by
      exact (to_succ (S := S) e' 1 4 8).1 <| by
        simpa [e', e, consEnv] using hCsuccDb
    have hRel1 : irel d' b' d₀ d' := by
      exact (to_relQuad (S := S) e' 0 2 3 0).1 <| by
        simpa [e', e, consEnv] using hRel1Db
    have hRel2 : irel a b' c' d' := by
      exact (to_relQuad (S := S) e' 6 2 1 0).1 <| by
        simpa [e', e, consEnv] using hRel2Db
    have hLess : iless d' d₀ := by
      exact (to_less (S := S) e' 0 3).1 <| by
        simpa [e', e, consEnv] using hLessDb
    have hbPred := vpSucc (S := S) (ρ := ρ) (m := m) (z := z) vSucc hBsucc
    have hcPred := vpSucc (S := S) (ρ := ρ) (m := m) (z := z) vSucc hCsucc
    have hb'm : ileq b' m := by
      exact leq_trans (S := S) (ρ := ρ) (m := m) (z := z) vTrans hbPred.1.1 hbm
    have hd'm : ileq d' m := by
      exact leq_trans (S := S) (ρ := ρ) (m := m) (z := z) vTrans hLess.1 hdm
    have hc'm : ileq c' m := by
      exact leq_trans (S := S) (ρ := ρ) (m := m) (z := z) vTrans hcPred.1.1 hcm
    rcases IH b' hbPred.1 d' d₀ d' nm f hChain'
      hb'm
      hRel1
      hd'm
      hdm
      hd'm with
      ⟨nd', nb'', nd, nd'', hSem1, hfd', hfb', hfd, hfd''⟩
    rcases IH b' hbPred.1 a c' d' nm f hChain'
      hb'm
      hRel2
      ham
      hc'm
      hd'm with
      ⟨na, nb''', nc', nd''', hSem2, hfa, hfb'', hfc', hfd'''⟩
    have hndEq : nd'' = nd' := by
      exact Option.some.inj (hfd''.symm.trans hfd')
    have hndEq' : nd''' = nd' := by
      exact Option.some.inj (hfd'''.symm.trans hfd')
    have hnbEq : nb''' = nb'' := by
      exact Option.some.inj (hfb''.symm.trans hfb')
    have hfb : f b = some (Nat.succ nb'') := by
      cases hfbCur : f b with
      | none =>
          exfalso
          exact (hDom b).1 hbm hfbCur
      | some nb =>
          have hStep := (hSuccStep b' b nb'' nb hfb' hfbCur).2 hBsucc
          exact congrArg some hStep.symm
    have hfc : f c = some (Nat.succ nc') := by
      cases hfcCur : f c with
      | none =>
          exfalso
          exact (hDom c).1 hcm hfcCur
      | some nc =>
          have hStep := (hSuccStep c' c nc' nc hfc' hfcCur).2 hCsucc
          exact congrArg some hStep.symm
    rcases hSem1 with ⟨hSem1a, hSem1b⟩
    rcases hSem2 with ⟨hSem2a, hSem2b⟩
    subst nd''
    subst nd'''
    subst nb'''
    have hfdFinal : f d₀ = some (1 + nb'' + nd') := by
      have hnd : nd = 1 + nb'' + nd' := by omega
      rw [hfd, hnd]
    refine ⟨na, Nat.succ nb'', Nat.succ nc', 1 + nb'' + nd', ?_⟩
    refine ⟨?_, hfa, hfb, hfc, hfdFinal⟩
    constructor
    · omega
    · calc
        Nat.succ nb'' * (1 + Nat.succ nb'')
            = nb'' * (1 + nb'') + 2 * nb'' + 2 := by
                rw [show 1 + Nat.succ nb'' = Nat.succ (Nat.succ nb'') by omega]
                rw [Nat.mul_succ, Nat.succ_mul]
                ring_nf
                omega
        _ = (nd' + nd') + 2 * nb'' + 2 := by rw [hSem1b]
        _ = (1 + nb'' + nd') + (1 + nb'' + nd') := by omega

theorem translate_single_correct
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans)
    (vSucc : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aSucc 1))
    (vDescr : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aDescr 1))
    (vDescr2 : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aDescr2 1))
    {e : Nat → S.D} {h10v : H10UPC} {zz n : Nat} {f : S.D → Option Nat}
    (hVar : highestVar h10v < zz)
    (hChain : chain z m n f)
    (hShift : ∀ k, consEnv m (consEnv z ρ) k = e (k + zz))
    (hSat : dbSatisfies S e (DBFormula.translateSingle h10v zz)) :
    h10upcSem (fun k => chainEnv f (e k)) h10v := by
  rcases h10v with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  have ha : a < zz := lt_of_le_of_lt (leftVar_le_highestVar ((a, b), (c, d))) hVar
  have hb : b < zz := lt_of_le_of_lt (rightVar_le_highestVar ((a, b), (c, d))) hVar
  have hc : c < zz := lt_of_le_of_lt (thirdVar_le_highestVar ((a, b), (c, d))) hVar
  have hd : d < zz := lt_of_le_of_lt (fourthVar_le_highestVar ((a, b), (c, d))) hVar
  have hSat' := hSat
  simp [DBFormula.translateSingle, DBFormula.conjs] at hSat'
  rcases hSat' with ⟨hRel, hLeA, hLeB, hLeC, hLeD⟩
  have hmEq : e zz = m := by
    simpa [Nat.zero_add, consEnv] using (hShift 0).symm
  have hA : ileq (e a) m := by
    simpa [hmEq] using (to_leq (S := S) e a zz).1 hLeA
  have hB : ileq (e b) m := by
    simpa [hmEq] using (to_leq (S := S) e b zz).1 hLeB
  have hC : ileq (e c) m := by
    simpa [hmEq] using (to_leq (S := S) e c zz).1 hLeC
  have hD : ileq (e d) m := by
    simpa [hmEq] using (to_leq (S := S) e d zz).1 hLeD
  have hRel' : irel (e a) (e b) (e c) (e d) := (to_relQuad (S := S) e a b c d).1 hRel
  rcases chain_proves (S := S) (ρ := ρ) (m := m) (z := z)
      vTrans vSucc vDescr vDescr2 hChain hB hRel' hA hC hD with
    ⟨na, nb, nc, nd, hSem, hfa, hfb, hfc, hfd⟩
  simpa [h10upcSem, chainEnv, hfa, hfb, hfc, hfd] using hSem

theorem translate_list_correct
    (vTrans : dbSatisfies S (consEnv m (consEnv z ρ)) DBFormula.aTrans)
    (vSucc : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aSucc 1))
    (vDescr : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aDescr 1))
    (vDescr2 : dbSatisfies S (consEnv m (consEnv z ρ)) (DBFormula.aDescr2 1))
    {e : Nat → S.D} {zz n : Nat} {f : S.D → Option Nat} {cs : List H10UPC}
    (hVar : highestVarList cs < zz)
    (hChain : chain z m n f)
    (hShift : ∀ k, consEnv m (consEnv z ρ) k = e (k + zz))
    (hSat : dbSatisfies S e (DBFormula.translateList zz cs)) :
    ∀ h10v, h10v ∈ cs → h10upcSem (fun k => chainEnv f (e k)) h10v := by
  induction cs generalizing e zz n f with
  | nil =>
      intro h10v hmem
      cases hmem
  | cons c cs ih =>
      have hSat' := hSat
      simp [DBFormula.translateList] at hSat'
      rcases hSat' with ⟨hHead, hTail⟩
      intro h10v hmem
      have hmem' : h10v = c ∨ h10v ∈ cs := by
        simpa [List.mem_cons] using hmem
      rcases hmem' with hEq | hmem
      · subst hEq
        apply translate_single_correct (S := S) (ρ := ρ) (m := m) (z := z)
          vTrans vSucc vDescr vDescr2
        · exact lt_of_le_of_lt (Nat.le_max_left _ _) hVar
        · exact hChain
        · exact hShift
        · exact hHead
      · apply ih
        · exact lt_of_le_of_lt (Nat.le_max_right _ _) hVar
        · exact hChain
        · exact hShift
        · exact hTail
        · exact hmem

end WithAxioms

end InverseTransport

def witnessBaseEnv (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ)) :
    Nat → Model (transportBound cs ρ) :=
  consEnv
    (Model.num ⟨transportBound cs ρ, le_rfl⟩)
    (consEnv (Model.num ⟨0, Nat.zero_le _⟩) tail)

def translatedConstraintEnv (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ)) :
    Nat → Model (transportBound cs ρ) :=
  emplacedEnv (Nat.succ (highestVarList cs))
    (transportAssignment cs ρ)
    (witnessBaseEnv cs ρ tail)

theorem translatedConstraintEnv_desc
    (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ))
    (i : Nat) (hi : i ≤ highestVarList cs) :
    ∃ h : ρ i ≤ transportBound cs ρ,
      translatedConstraintEnv cs ρ tail i = Model.num ⟨ρ i, h⟩ := by
  have hiLt : i < Nat.succ (highestVarList cs) := Nat.lt_succ_of_le hi
  rcases transportAssignment_desc cs ρ i hi with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  simpa [translatedConstraintEnv, hiLt] using
    congrArg (fun x => x) hh

@[simp] theorem translatedConstraintEnv_bound
    (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ)) :
    translatedConstraintEnv cs ρ tail (Nat.succ (highestVarList cs)) =
      Model.num ⟨transportBound cs ρ, le_rfl⟩ := by
  have hge : Nat.succ (highestVarList cs) ≤ Nat.succ (highestVarList cs) := le_rfl
  simp [translatedConstraintEnv, witnessBaseEnv, emplacedEnv_ge, hge]

theorem dbSatisfies_translateSingle_of_mem
    (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ))
    (c : H10UPC) (hc : c ∈ cs)
    (hSat : h10upcSem ρ c) :
    dbSatisfies (canonicalStructure (transportBound cs ρ))
      (translatedConstraintEnv cs ρ tail)
      (DBFormula.translateSingle c (Nat.succ (highestVarList cs))) := by
  rcases c with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  have hMax : highestVar ((a, b), (c, d)) ≤ highestVarList cs :=
    highestVar_le_highestVarList hc
  have ha : a ≤ highestVarList cs := le_trans (leftVar_le_highestVar ((a, b), (c, d))) hMax
  have hb : b ≤ highestVarList cs := le_trans (rightVar_le_highestVar ((a, b), (c, d))) hMax
  have hc' : c ≤ highestVarList cs := le_trans (thirdVar_le_highestVar ((a, b), (c, d))) hMax
  have hd : d ≤ highestVarList cs := le_trans (fourthVar_le_highestVar ((a, b), (c, d))) hMax
  rcases translatedConstraintEnv_desc cs ρ tail a ha with ⟨ua, hEa⟩
  rcases translatedConstraintEnv_desc cs ρ tail b hb with ⟨ub, hEb⟩
  rcases translatedConstraintEnv_desc cs ρ tail c hc' with ⟨uc, hEc⟩
  rcases translatedConstraintEnv_desc cs ρ tail d hd with ⟨ud, hEd⟩
  have hEm :
      translatedConstraintEnv cs ρ tail (Nat.succ (highestVarList cs)) =
        Model.num ⟨transportBound cs ρ, le_rfl⟩ :=
    translatedConstraintEnv_bound cs ρ tail
  have hRel :
      dbSatisfies (canonicalStructure (transportBound cs ρ))
        (translatedConstraintEnv cs ρ tail) (DBFormula.relQuad a b c d) := by
    refine (dbSatisfies_relQuad_num_iff _ _ _ _ _ _ _ _ _ _ hEa hEb hEc hEd).2 ?_
    simpa [h10upcSem, h10upcSemDirect] using hSat
  have hLeA :
      dbSatisfies (canonicalStructure (transportBound cs ρ))
        (translatedConstraintEnv cs ρ tail)
        (DBFormula.leq a (Nat.succ (highestVarList cs))) := by
    refine (dbSatisfies_leq_num_iff _ _ _ _ _ _ hEa hEm).2 ?_
    simpa using ua
  have hLeB :
      dbSatisfies (canonicalStructure (transportBound cs ρ))
        (translatedConstraintEnv cs ρ tail)
        (DBFormula.leq b (Nat.succ (highestVarList cs))) := by
    refine (dbSatisfies_leq_num_iff _ _ _ _ _ _ hEb hEm).2 ?_
    simpa using ub
  have hLeC :
      dbSatisfies (canonicalStructure (transportBound cs ρ))
        (translatedConstraintEnv cs ρ tail)
        (DBFormula.leq c (Nat.succ (highestVarList cs))) := by
    refine (dbSatisfies_leq_num_iff _ _ _ _ _ _ hEc hEm).2 ?_
    simpa using uc
  have hLeD :
      dbSatisfies (canonicalStructure (transportBound cs ρ))
        (translatedConstraintEnv cs ρ tail)
        (DBFormula.leq d (Nat.succ (highestVarList cs))) := by
    refine (dbSatisfies_leq_num_iff _ _ _ _ _ _ hEd hEm).2 ?_
    simpa using ud
  simpa [DBFormula.translateSingle, DBFormula.conjs] using
    And.intro hRel (And.intro hLeA (And.intro hLeB (And.intro hLeC hLeD)))

theorem dbSatisfies_translateList_of_subset
    (fullCs subCs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound fullCs ρ))
    (hSub : ∀ c, c ∈ subCs → c ∈ fullCs)
    (hSat : ∀ c, c ∈ subCs → h10upcSem ρ c) :
    dbSatisfies (canonicalStructure (transportBound fullCs ρ))
      (translatedConstraintEnv fullCs ρ tail)
      (DBFormula.translateList (Nat.succ (highestVarList fullCs)) subCs) := by
  induction subCs with
  | nil =>
      simp [DBFormula.translateList, dbSatisfies]
  | cons c cs ih =>
      refine And.intro ?_ ?_
      · apply dbSatisfies_translateSingle_of_mem (cs := fullCs) (ρ := ρ) (tail := tail)
        · exact hSub c (by simp)
        · exact hSat c (by simp)
      · apply ih
        · intro c hc
          exact hSub c (by simp [hc])
        · intro c hc
          exact hSat c (by simp [hc])

theorem dbSatisfies_translateList_of
    (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ))
    (hSat : ∀ c, c ∈ cs → h10upcSem ρ c) :
    dbSatisfies (canonicalStructure (transportBound cs ρ))
      (translatedConstraintEnv cs ρ tail)
      (DBFormula.translateList (Nat.succ (highestVarList cs)) cs) :=
  dbSatisfies_translateList_of_subset cs cs ρ tail (by intro c hc; exact hc) hSat

theorem dbSatisfies_emplacedTranslateList_of
    (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ))
    (hSat : ∀ c, c ∈ cs → h10upcSem ρ c) :
    dbSatisfies (canonicalStructure (transportBound cs ρ))
      (witnessBaseEnv cs ρ tail)
      (DBFormula.emplaceExists (Nat.succ (highestVarList cs))
        (DBFormula.translateList (Nat.succ (highestVarList cs)) cs)) := by
  exact dbSatisfies_emplaceExists_of
    (canonicalStructure (transportBound cs ρ))
    (witnessBaseEnv cs ρ tail)
    (transportAssignment cs ρ)
    (Nat.succ (highestVarList cs))
    (DBFormula.translateList (Nat.succ (highestVarList cs)) cs)
    (dbSatisfies_translateList_of cs ρ tail hSat)

theorem dbSatisfies_aTrans
    (m : Nat) (ρ : Nat → Model m) :
    dbSatisfies (canonicalStructure m) ρ DBFormula.aTrans := by
  intro x
  intro y
  intro z
  let ρ' : Nat → Model m := consEnv z (consEnv y (consEnv x ρ))
  intro h21
  intro h10
  rcases (dbSatisfies_N_iff m ρ' 2).1 h21.1.1 with ⟨nx, hx⟩
  rcases (dbSatisfies_N_iff m ρ' 1).1 h21.1.2.1 with ⟨ny, hy⟩
  rcases (dbSatisfies_N_iff m ρ' 0).1 h10.1.2.1 with ⟨nz, hz⟩
  have hLt21 : nx.1 < ny.1 := by
    exact (dbSatisfies_less_num_iff m ρ' 2 1 nx ny hx hy).1 h21
  have hLt10 : ny.1 < nz.1 := by
    exact (dbSatisfies_less_num_iff m ρ' 1 0 ny nz hy hz).1 h10
  exact (dbSatisfies_less_num_iff m ρ' 2 0 nx nz hx hz).2 (lt_trans hLt21 hLt10)

theorem dbSatisfies_aPred_witnessBase
    (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ)) :
    dbSatisfies (canonicalStructure (transportBound cs ρ))
      (witnessBaseEnv cs ρ tail)
      (DBFormula.aPred 1) := by
  intro x
  intro hNx
  intro hNotDeq
  let M := transportBound cs ρ
  let ρ' : Nat → Model M := consEnv x (witnessBaseEnv cs ρ tail)
  let zFin : finNum M := ⟨0, Nat.zero_le M⟩
  rcases (dbSatisfies_N_iff M ρ' 0).1 hNx with ⟨nx, hnx⟩
  have hz : ρ' 2 = Model.num zFin := by
    simp [ρ', witnessBaseEnv, zFin]
  have hnx0 : nx.1 ≠ 0 := by
    intro hZero
    have hEq : zFin = nx := by
      ext
      simpa [zFin] using hZero.symm
    have hDeq :
        dbSatisfies (canonicalStructure M) ρ' (DBFormula.deq 2 0) := by
      exact (dbSatisfies_deq_num_iff M ρ' 2 0 zFin nx hz hnx).2 hEq
    exact hNotDeq hDeq
  have hnxPos : 0 < nx.1 := Nat.pos_of_ne_zero hnx0
  let predFin : finNum M := ⟨nx.1 - 1, le_trans (Nat.sub_le _ _) nx.2⟩
  refine ⟨Model.num predFin, ?_⟩
  let ρ'' : Nat → Model M := consEnv (Model.num predFin) ρ'
  have hPred : ρ'' 0 = Model.num predFin := by simp [ρ'']
  have hCur : ρ'' 1 = Model.num nx := by simpa [ρ'', ρ'] using hnx
  have hZeroEnv : ρ'' 3 = Model.num zFin := by simp [ρ'', ρ', witnessBaseEnv, zFin]
  refine (dbSatisfies_relQuad_num_iff M ρ'' 0 3 1 3 predFin zFin nx zFin
    hPred hZeroEnv hCur hZeroEnv).2 ?_
  dsimp [predFin, zFin, h10upcSemDirect]
  omega

theorem dbSatisfies_aSucc_witnessBase
    (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ)) :
    dbSatisfies (canonicalStructure (transportBound cs ρ))
      (witnessBaseEnv cs ρ tail)
      (DBFormula.aSucc 1) := by
  intro l
  intro r
  let M := transportBound cs ρ
  let ρ' : Nat → Model M := consEnv r (consEnv l (witnessBaseEnv cs ρ tail))
  intro hNl
  intro hNr
  intro hRel
  rcases (dbSatisfies_N_iff M ρ' 1).1 hNl with ⟨nl, hl⟩
  rcases (dbSatisfies_N_iff M ρ' 0).1 hNr with ⟨nr, hr⟩
  let zFin : finNum M := ⟨0, Nat.zero_le M⟩
  have hz : ρ' 3 = Model.num zFin := by
    simp [ρ', witnessBaseEnv, zFin]
  have hStep : h10upcSemDirect ((nl.1, zFin.1), (nr.1, zFin.1)) := by
    exact (dbSatisfies_relQuad_num_iff M ρ' 1 3 0 3 nl zFin nr zFin hl hz hr hz).1 hRel
  have hSuccEq' : nl.1 + 1 = nr.1 := by
    simpa [h10upcSemDirect, zFin, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStep.1
  have hSuccEq : nr.1 = nl.1 + 1 := by
    exact hSuccEq'.symm
  have hLtLR : nl.1 < nr.1 := by
    rw [hSuccEq]
    exact Nat.lt_succ_self _
  refine ⟨?_, ?_⟩
  · exact (dbSatisfies_less_num_iff M ρ' 1 0 nl nr hl hr).2 hLtLR
  · intro k
    let ρ'' : Nat → Model M := consEnv k ρ'
    intro hLess
    rcases (dbSatisfies_N_iff M ρ'' 0).1 hLess.1.1 with ⟨nk, hk⟩
    have hr' : ρ'' 1 = Model.num nr := by simpa [ρ'', ρ'] using hr
    have hl' : ρ'' 2 = Model.num nl := by simpa [ρ'', ρ'] using hl
    have hlt : nk.1 < nr.1 := by
      exact (dbSatisfies_less_num_iff M ρ'' 0 1 nk nr hk hr').1 hLess
    have hlt' : nk.1 < nl.1 + 1 := by simpa [hSuccEq] using hlt
    exact (dbSatisfies_leq_num_iff M ρ'' 0 2 nk nl hk hl').2 (Nat.le_of_lt_succ hlt')

theorem dbSatisfies_aDescr2_witnessBase
    (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ)) :
    dbSatisfies (canonicalStructure (transportBound cs ρ))
      (witnessBaseEnv cs ρ tail)
      (DBFormula.aDescr2 1) := by
  intro a
  intro b
  intro c
  intro d
  let M := transportBound cs ρ
  let ρ' : Nat → Model M := consEnv d (consEnv c (consEnv b (consEnv a (witnessBaseEnv cs ρ tail))))
  intro hNa
  intro hNb
  intro hNc
  intro hNd
  intro hRel
  intro hDeq
  rcases (dbSatisfies_N_iff M ρ' 3).1 hNa with ⟨na, ha⟩
  rcases (dbSatisfies_N_iff M ρ' 2).1 hNb with ⟨nb, hb⟩
  rcases (dbSatisfies_N_iff M ρ' 1).1 hNc with ⟨nc, hc⟩
  rcases (dbSatisfies_N_iff M ρ' 0).1 hNd with ⟨nd, hd⟩
  let zFin : finNum M := ⟨0, Nat.zero_le M⟩
  have hz : ρ' 5 = Model.num zFin := by
    simp [ρ', witnessBaseEnv, zFin]
  have hRelSem : h10upcSemDirect ((na.1, nb.1), (nc.1, nd.1)) := by
    exact (dbSatisfies_relQuad_num_iff M ρ' 3 2 1 0 na nb nc nd ha hb hc hd).1 hRel
  have hBZero : nb = zFin := by
    exact (dbSatisfies_deq_num_iff M ρ' 2 5 nb zFin hb hz).1 hDeq
  have hDZeroVal : nd.1 = 0 := by
    have hNbZero : nb.1 = 0 := congrArg Subtype.val hBZero
    have hEq2 : nd.1 + nd.1 = 0 := by
      simpa [h10upcSemDirect, hNbZero, Nat.zero_mul] using hRelSem.2.symm
    exact Nat.eq_zero_of_add_eq_zero_left hEq2
  have hDZero : nd = zFin := by
    ext
    simpa [zFin] using hDZeroVal
  exact (dbSatisfies_deq_num_iff M ρ' 0 5 nd zFin hd hz).2 hDZero

theorem dbSatisfies_aDescr_witnessBase
    (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ)) :
    dbSatisfies (canonicalStructure (transportBound cs ρ))
      (witnessBaseEnv cs ρ tail)
      (DBFormula.aDescr 1) := by
  intro a
  intro b
  intro c
  intro d
  let M := transportBound cs ρ
  let ρ' : Nat → Model M := consEnv d (consEnv c (consEnv b (consEnv a (witnessBaseEnv cs ρ tail))))
  intro hNa
  intro hNb
  intro hNc
  intro hNd
  intro hNotDeq
  intro hRel
  rcases (dbSatisfies_N_iff M ρ' 3).1 hNa with ⟨na, ha⟩
  rcases (dbSatisfies_N_iff M ρ' 2).1 hNb with ⟨nb, hb⟩
  rcases (dbSatisfies_N_iff M ρ' 1).1 hNc with ⟨nc, hc⟩
  rcases (dbSatisfies_N_iff M ρ' 0).1 hNd with ⟨nd, hd⟩
  let zFin : finNum M := ⟨0, Nat.zero_le M⟩
  have hz : ρ' 5 = Model.num zFin := by
    simp [ρ', witnessBaseEnv, zFin]
  have hRelSem : h10upcSemDirect ((na.1, nb.1), (nc.1, nd.1)) := by
    exact (dbSatisfies_relQuad_num_iff M ρ' 3 2 1 0 na nb nc nd ha hb hc hd).1 hRel
  have hNbNe : nb ≠ zFin := by
    intro hEq
    have hDeq :
        dbSatisfies (canonicalStructure M) ρ' (DBFormula.deq 5 2) := by
      exact (dbSatisfies_deq_num_iff M ρ' 5 2 zFin nb hz hb).2 hEq.symm
    exact hNotDeq hDeq
  have hNbPos : 0 < nb.1 := by
    exact Nat.pos_iff_ne_zero.mpr (by
      intro hZero
      apply hNbNe
      ext
      simpa [zFin] using hZero)
  have hNcEq : nc.1 = 1 + na.1 + nb.1 := by
    simpa [h10upcSemDirect] using hRelSem.1.symm
  have hNcPos : 0 < nc.1 := by
    nlinarith [hNcEq]
  have hNdEq : nb.1 * (1 + nb.1) = nd.1 + nd.1 := by
    simpa [h10upcSemDirect] using hRelSem.2
  let bPred : finNum M := ⟨nb.1 - 1, le_trans (Nat.sub_le _ _) nb.2⟩
  let cPred : finNum M := ⟨nc.1 - 1, le_trans (Nat.sub_le _ _) nc.2⟩
  let tFin : finNum M := ⟨nd.1 - nb.1, le_trans (Nat.sub_le _ _) nd.2⟩
  have hNbSucc : nb.1 = bPred.1 + 1 := by
    dsimp [bPred]
    exact (Nat.succ_pred_eq_of_pos hNbPos).symm
  have hNcSucc : nc.1 = cPred.1 + 1 := by
    dsimp [cPred]
    exact (Nat.succ_pred_eq_of_pos hNcPos).symm
  have hNbLeNd : nb.1 ≤ nd.1 := by
    nlinarith [hNdEq, hNbPos]
  have hRelTDom : 1 + tFin.1 + bPred.1 = nd.1 := by
    have hTAdd : tFin.1 + nb.1 = nd.1 := by
      dsimp [tFin]
      exact Nat.sub_add_cancel hNbLeNd
    calc
      1 + tFin.1 + bPred.1 = tFin.1 + (bPred.1 + 1) := by omega
      _ = tFin.1 + nb.1 := by rw [hNbSucc]
      _ = nd.1 := hTAdd
  have hRelTQuad : bPred.1 * (1 + bPred.1) = tFin.1 + tFin.1 := by
    dsimp [tFin, bPred]
    nlinarith [hNdEq, hNbPos, hNbLeNd]
  have hRelADom : 1 + na.1 + bPred.1 = cPred.1 := by
    dsimp [bPred, cPred]
    nlinarith [hNcEq, hNbPos]
  have hTLt : tFin.1 < nd.1 := by
    have hNdPos : 0 < nd.1 := lt_of_lt_of_le hNbPos hNbLeNd
    dsimp [tFin]
    exact Nat.sub_lt hNdPos hNbPos
  refine ⟨Model.num bPred, ?_⟩
  refine ⟨Model.num cPred, ?_⟩
  refine ⟨Model.num tFin, ?_⟩
  let ρ'' : Nat → Model M := consEnv (Model.num tFin) (consEnv (Model.num cPred) (consEnv (Model.num bPred) ρ'))
  have h0 : ρ'' 0 = Model.num tFin := by simp [ρ'']
  have h1 : ρ'' 1 = Model.num cPred := by simp [ρ'']
  have h2 : ρ'' 2 = Model.num bPred := by simp [ρ'']
  have h3 : ρ'' 3 = Model.num nd := by simpa [ρ'', ρ'] using hd
  have h4 : ρ'' 4 = Model.num nc := by simpa [ρ'', ρ'] using hc
  have h5 : ρ'' 5 = Model.num nb := by simpa [ρ'', ρ'] using hb
  have h6 : ρ'' 6 = Model.num na := by simpa [ρ'', ρ'] using ha
  have h8 : ρ'' 8 = Model.num zFin := by simp [ρ'', ρ', witnessBaseEnv, zFin]
  have hSuccB :
      dbSatisfies (canonicalStructure M) ρ'' (DBFormula.succ 2 5 8) := by
    refine (dbSatisfies_relQuad_num_iff M ρ'' 2 8 5 8 bPred zFin nb zFin h2 h8 h5 h8).2 ?_
    dsimp [h10upcSemDirect, bPred, zFin]
    omega
  have hSuccC :
      dbSatisfies (canonicalStructure M) ρ'' (DBFormula.succ 1 4 8) := by
    refine (dbSatisfies_relQuad_num_iff M ρ'' 1 8 4 8 cPred zFin nc zFin h1 h8 h4 h8).2 ?_
    dsimp [h10upcSemDirect, cPred, zFin]
    omega
  have hRelT :
      dbSatisfies (canonicalStructure M) ρ'' (DBFormula.relQuad 0 2 3 0) := by
    refine (dbSatisfies_relQuad_num_iff M ρ'' 0 2 3 0 tFin bPred nd tFin h0 h2 h3 h0).2 ?_
    exact ⟨hRelTDom, hRelTQuad⟩
  have hRelA :
      dbSatisfies (canonicalStructure M) ρ'' (DBFormula.relQuad 6 2 1 0) := by
    refine (dbSatisfies_relQuad_num_iff M ρ'' 6 2 1 0 na bPred cPred tFin h6 h2 h1 h0).2 ?_
    exact ⟨hRelADom, hRelTQuad⟩
  have hLess :
      dbSatisfies (canonicalStructure M) ρ'' (DBFormula.less 0 3) := by
    exact (dbSatisfies_less_num_iff M ρ'' 0 3 tFin nd h0 h3).2 hTLt
  simpa [DBFormula.conjs] using
    And.intro hSuccB (And.intro hSuccC (And.intro hRelT (And.intro hRelA hLess)))

theorem dbSatisfies_sourceF_of
    (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ))
    (hSat : ∀ c, c ∈ cs → h10upcSem ρ c) :
    dbSatisfies (canonicalStructure (transportBound cs ρ))
      tail
      (DBFormula.sourceF cs) := by
  let M := transportBound cs ρ
  let zFin : finNum M := ⟨0, Nat.zero_le M⟩
  let topFin : finNum M := ⟨M, le_rfl⟩
  have hBody :
      dbSatisfies (canonicalStructure M)
        (witnessBaseEnv cs ρ tail)
        (DBFormula.conjs
          [DBFormula.aTrans,
           DBFormula.aPred 1,
           DBFormula.aSucc 1,
           DBFormula.aDescr 1,
           DBFormula.aDescr2 1,
           DBFormula.emplaceExists (Nat.succ (highestVarList cs))
             (DBFormula.translateList (Nat.succ (highestVarList cs)) cs)]) := by
    simpa [DBFormula.conjs] using
      And.intro
        (dbSatisfies_aTrans M (witnessBaseEnv cs ρ tail))
        (And.intro
          (dbSatisfies_aPred_witnessBase cs ρ tail)
          (And.intro
            (dbSatisfies_aSucc_witnessBase cs ρ tail)
            (And.intro
              (dbSatisfies_aDescr_witnessBase cs ρ tail)
              (And.intro
                (dbSatisfies_aDescr2_witnessBase cs ρ tail)
                (dbSatisfies_emplacedTranslateList_of cs ρ tail hSat)))))
  refine ⟨Model.num zFin, ?_⟩
  refine ⟨Model.num topFin, ?_⟩
  simpa [DBFormula.sourceF, witnessBaseEnv, zFin, topFin] using hBody

theorem not_dbSatisfies_sourceReductionFormula_of
    (cs : List H10UPC) (ρ : Nat → Nat)
    (tail : Nat → Model (transportBound cs ρ))
    (hSat : ∀ c, c ∈ cs → h10upcSem ρ c) :
    ¬ dbSatisfies (canonicalStructure (transportBound cs ρ))
      tail
      (DBFormula.sourceReductionFormula cs) := by
  intro hFormula
  exact hFormula (dbSatisfies_sourceF_of cs ρ tail hSat)

theorem h10upcSat_of_dbSatisfies_sourceF
    (S : ClassicalStructure ReductionSig) [Finite S.D]
    (ρ : Nat → S.D) (cs : List H10UPC)
    (hSource : dbSatisfies S ρ (DBFormula.sourceF cs)) :
    H10UPCSat cs := by
  rcases hSource with ⟨z, m, hBody⟩
  have hBody' := hBody
  simp [DBFormula.sourceF, DBFormula.conjs] at hBody'
  rcases hBody' with ⟨vTrans, vPred, vSucc, vDescr, vDescr2, hList⟩
  rcases remove_emplaceExists S (consEnv m (consEnv z ρ))
      (Nat.succ (highestVarList cs))
      (DBFormula.translateList (Nat.succ (highestVarList cs)) cs) hList with
    ⟨ρ2, hListSat, hShift⟩
  have hSatOrNm : H10UPCSat cs ∨ iN (S := S) m := by
    cases cs with
    | nil =>
        left
        refine ⟨fun _ => 0, ?_⟩
        intro c hc
        cases hc
    | cons c cs =>
        right
        have hHead :
            dbSatisfies S ρ2
              (DBFormula.translateSingle c (Nat.succ (highestVarList (c :: cs)))) := by
          simpa [DBFormula.translateList] using hListSat.1
        have hmEq : ρ2 (Nat.succ (highestVarList (c :: cs))) = m := by
          simpa [Nat.zero_add, consEnv] using (hShift 0).symm
        have hHead' := hHead
        simp [DBFormula.translateSingle, DBFormula.conjs] at hHead'
        rcases hHead' with ⟨_hRel, _hLeA, hLeB, _hLeC, _hLeD⟩
        have hLe := (to_leq (S := S) ρ2 c.1.2 (Nat.succ (highestVarList (c :: cs)))).1 hLeB
        simpa [hmEq, iN] using hLe.2.1
  rcases hSatOrNm with hSat | hNm
  · exact hSat
  · rcases mkchain (S := S) (ρ := ρ) (m := m) (z := z) vTrans vPred vSucc hNm with
      ⟨n, f, hChain⟩
    refine ⟨fun k => chainEnv f (ρ2 k), ?_⟩
    have hListCorrect :=
      translate_list_correct (S := S) (ρ := ρ) (m := m) (z := z)
        vTrans vSucc vDescr vDescr2
        (cs := cs) (e := ρ2) (zz := Nat.succ (highestVarList cs)) (n := n) (f := f)
        (Nat.lt_succ_self _) hChain hShift hListSat
    intro c hc
    exact hListCorrect c hc

end NativeFiniteValidity

theorem h10upcFiniteValidityFormula_correct_forward (cs : List H10UPC) :
    finiteFOLValid (h10upcFiniteValidityFormula cs) → ¬ H10UPCSat cs := by
  intro hFinite hSat
  rcases hSat with ⟨ρ, hρ⟩
  let M := NativeFiniteValidity.transportBound cs ρ
  let tail : Nat → Model M := fun _ => Model.num ⟨0, Nat.zero_le M⟩
  letI : Finite (NativeFiniteValidity.canonicalStructure M).D := by
    dsimp [NativeFiniteValidity.canonicalStructure]
    infer_instance
  have hLocal :
      ClassicalStructure.satisfies (NativeFiniteValidity.canonicalStructure M) tail
        (h10upcFiniteValidityFormula cs) := by
    simpa [h10upcFiniteValidityFormula] using
      hFinite (NativeFiniteValidity.canonicalStructure M) tail
  have hDb :
      NativeFiniteValidity.dbSatisfies (NativeFiniteValidity.canonicalStructure M) tail
        (NativeFiniteValidity.DBFormula.sourceReductionFormula cs) := by
    have hScoped := NativeFiniteValidity.wellScoped_sourceReductionFormula cs
    have hAt :
        ClassicalStructure.satisfies (NativeFiniteValidity.canonicalStructure M)
          (NativeFiniteValidity.assignOfEnv (NativeFiniteValidity.canonicalStructure M) 0 tail tail)
          (NativeFiniteValidity.DBFormula.toLocal 0
            (NativeFiniteValidity.DBFormula.sourceReductionFormula cs)) := by
      simpa [NativeFiniteValidity.assignOfEnv_zero, h10upcFiniteValidityFormula] using hLocal
    exact
      (NativeFiniteValidity.dbSatisfies_toLocal_iff (NativeFiniteValidity.canonicalStructure M) 0 tail tail
        (φ := NativeFiniteValidity.DBFormula.sourceReductionFormula cs) hScoped).mp hAt
  exact
    (NativeFiniteValidity.not_dbSatisfies_sourceReductionFormula_of cs ρ tail hρ) hDb

theorem h10upcFiniteValidityFormula_complete (cs : List H10UPC) :
    ¬ H10UPCSat cs → finiteFOLValid (h10upcFiniteValidityFormula cs) := by
  intro hUnsat S _ g
  by_contra hBad
  have hScoped := NativeFiniteValidity.wellScoped_sourceReductionFormula cs
  have hDbBad :
      ¬ NativeFiniteValidity.dbSatisfies S g
        (NativeFiniteValidity.DBFormula.sourceReductionFormula cs) := by
    intro hDb
    have hSat :
        ClassicalStructure.satisfies S g (h10upcFiniteValidityFormula cs) := by
      have hLocal :=
        (NativeFiniteValidity.dbSatisfies_toLocal_iff S 0 g g
          (φ := NativeFiniteValidity.DBFormula.sourceReductionFormula cs) hScoped).mpr hDb
      simpa [NativeFiniteValidity.assignOfEnv_zero, h10upcFiniteValidityFormula] using hLocal
    exact hBad hSat
  have hSource :
      NativeFiniteValidity.dbSatisfies S g (NativeFiniteValidity.DBFormula.sourceF cs) := by
    by_cases hAnte :
        NativeFiniteValidity.dbSatisfies S g (NativeFiniteValidity.DBFormula.sourceF cs)
    · exact hAnte
    · exfalso
      apply hDbBad
      intro hSrc
      exact hAnte hSrc
  exact hUnsat (NativeFiniteValidity.h10upcSat_of_dbSatisfies_sourceF S g cs hSource)

end InqBQ
end HeytingLean
