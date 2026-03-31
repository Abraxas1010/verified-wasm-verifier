import HeytingLean.InqBQ.Computability
import HeytingLean.InqBQ.FiniteValidityBridge
import Mathlib.Computability.Halting
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

namespace HeytingLean
namespace InqBQ

open Nat.Partrec

/-- Interpret a finite list of values as a total valuation by padding with zeros. -/
def valuationOfList (vals : List Nat) : Nat → Nat :=
  fun i => vals.getD i 0

/-- A finite list witnesses `H10UPCSat` when its induced valuation satisfies every constraint. -/
def listWitness : List H10UPC → List Nat → Prop
  | [], _ => True
  | c :: cs, vals => h10upcSem (valuationOfList vals) c ∧ listWitness cs vals

lemma leftVar_le_highestVar (c : H10UPC) : c.1.1 ≤ highestVar c := by
  rcases c with ⟨⟨x, y⟩, ⟨z₁, z₂⟩⟩
  exact le_max_left x (max y (max z₁ z₂))

lemma rightVar_le_highestVar (c : H10UPC) : c.1.2 ≤ highestVar c := by
  rcases c with ⟨⟨x, y⟩, ⟨z₁, z₂⟩⟩
  exact le_trans (le_max_left y (max z₁ z₂)) (le_max_right x (max y (max z₁ z₂)))

lemma thirdVar_le_highestVar (c : H10UPC) : c.2.1 ≤ highestVar c := by
  rcases c with ⟨⟨x, y⟩, ⟨z₁, z₂⟩⟩
  exact
    le_trans
      (le_trans (le_max_left z₁ z₂) (le_max_right y (max z₁ z₂)))
      (le_max_right x (max y (max z₁ z₂)))

lemma fourthVar_le_highestVar (c : H10UPC) : c.2.2 ≤ highestVar c := by
  rcases c with ⟨⟨x, y⟩, ⟨z₁, z₂⟩⟩
  exact
    le_trans
      (le_trans (le_max_right z₁ z₂) (le_max_right y (max z₁ z₂)))
      (le_max_right x (max y (max z₁ z₂)))

lemma highestVar_le_highestVarList {cs : List H10UPC} {c : H10UPC} (hc : c ∈ cs) :
    highestVar c ≤ highestVarList cs := by
  induction cs with
  | nil =>
      cases hc
  | cons d ds ih =>
      rw [highestVarList]
      have hc' : c = d ∨ c ∈ ds := by simpa using hc
      rcases hc' with rfl | hc'
      · exact le_max_left _ _
      · exact le_trans (ih hc') (le_max_right _ _)

lemma valuationOfList_ofFn (ρ : Nat → Nat) {n k : Nat} (hk : k < n) :
    valuationOfList (List.ofFn (fun i : Fin n => ρ i)) k = ρ k := by
  unfold valuationOfList
  have hk' : k < (List.ofFn (fun i : Fin n => ρ i)).length := by
    simpa [List.length_ofFn] using hk
  rw [List.getD_eq_getElem (l := List.ofFn (fun i : Fin n => ρ i)) (d := 0) hk']
  simpa using (List.getElem_ofFn (f := fun i : Fin n => ρ i) (i := k) hk')

lemma listWitness_iff_forall_mem (cs : List H10UPC) (vals : List Nat) :
    listWitness cs vals ↔ ∀ c, c ∈ cs → h10upcSem (valuationOfList vals) c := by
  induction cs with
  | nil =>
      simp [listWitness]
  | cons c cs ih =>
      constructor
      · rintro ⟨hc, hcs⟩ d hd
        have hd' : d = c ∨ d ∈ cs := by simpa using hd
        rcases hd' with rfl | hd
        · simpa using hc
        · exact (ih.mp hcs) d hd
      · intro h
        refine ⟨?_, ?_⟩
        · exact h c (by simp)
        · exact ih.mpr (fun d hd => h d (by simp [hd]))

instance instDecidableH10UPCSem (ρ : Nat → Nat) : DecidablePred (h10upcSem ρ) := by
  intro c
  cases c with
  | mk xy zw =>
      cases xy with
      | mk x y =>
          cases zw with
          | mk z₁ z₂ =>
              dsimp [h10upcSem, h10upcSemDirect]
              infer_instance

instance instDecidableListWitness (cs : List H10UPC) (vals : List Nat) :
    Decidable (listWitness cs vals) := by
  induction cs with
  | nil =>
      exact isTrue trivial
  | cons c cs ih =>
      by_cases hc : h10upcSem (valuationOfList vals) c
      · cases ih with
        | isTrue hcs =>
            exact isTrue ⟨hc, hcs⟩
        | isFalse hcs =>
            exact isFalse (fun h => hcs h.2)
      · exact isFalse (fun h => hc h.1)

theorem h10upcSat_iff_exists_listWitness (cs : List H10UPC) :
    H10UPCSat cs ↔ ∃ vals : List Nat, listWitness cs vals := by
  constructor
  · rintro ⟨ρ, hρ⟩
    set vals : List Nat := List.ofFn (fun i : Fin (highestVarList cs + 1) => ρ i) with hVals
    refine ⟨vals, (listWitness_iff_forall_mem cs vals).2 ?_⟩
    intro c hc
    have hcMax : highestVar c ≤ highestVarList cs := highestVar_le_highestVarList hc
    have hx : c.1.1 < highestVarList cs + 1 := Nat.lt_succ_of_le (le_trans (leftVar_le_highestVar c) hcMax)
    have hy : c.1.2 < highestVarList cs + 1 := Nat.lt_succ_of_le (le_trans (rightVar_le_highestVar c) hcMax)
    have hz₁ : c.2.1 < highestVarList cs + 1 := Nat.lt_succ_of_le (le_trans (thirdVar_le_highestVar c) hcMax)
    have hz₂ : c.2.2 < highestVarList cs + 1 := Nat.lt_succ_of_le (le_trans (fourthVar_le_highestVar c) hcMax)
    have hxv : valuationOfList vals c.1.1 = ρ c.1.1 := by
      rw [hVals]
      exact valuationOfList_ofFn ρ hx
    have hyv : valuationOfList vals c.1.2 = ρ c.1.2 := by
      rw [hVals]
      exact valuationOfList_ofFn ρ hy
    have hz₁v : valuationOfList vals c.2.1 = ρ c.2.1 := by
      rw [hVals]
      exact valuationOfList_ofFn ρ hz₁
    have hz₂v : valuationOfList vals c.2.2 = ρ c.2.2 := by
      rw [hVals]
      exact valuationOfList_ofFn ρ hz₂
    simpa [h10upcSem, h10upcSemDirect, hxv, hyv, hz₁v, hz₂v] using hρ c hc
  · rintro ⟨vals, hvals⟩
    exact ⟨valuationOfList vals, (listWitness_iff_forall_mem cs vals).1 hvals⟩

private theorem h10upcSem_primrecRel :
    PrimrecRel fun (c : H10UPC) (vals : List Nat) => h10upcSem (valuationOfList vals) c := by
  let xValFun : H10UPC × List Nat → Nat := fun p => List.getD p.2 p.1.1.1 0
  let yValFun : H10UPC × List Nat → Nat := fun p => List.getD p.2 p.1.1.2 0
  let z₁ValFun : H10UPC × List Nat → Nat := fun p => List.getD p.2 p.1.2.1 0
  let z₂ValFun : H10UPC × List Nat → Nat := fun p => List.getD p.2 p.1.2.2 0
  let lhs₁Fun : H10UPC × List Nat → Nat := fun p => 1 + xValFun p + yValFun p
  let lhs₂Fun : H10UPC × List Nat → Nat := fun p => yValFun p * (1 + yValFun p)
  let rhs₂Fun : H10UPC × List Nat → Nat := fun p => z₂ValFun p + z₂ValFun p
  have xVal : Primrec xValFun :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have yVal : Primrec yValFun :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have z₁Val : Primrec z₁ValFun :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have z₂Val : Primrec z₂ValFun :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have lhs₁ : Primrec lhs₁Fun :=
    (Primrec.nat_add.comp ((Primrec.nat_add.comp (Primrec.const 1) xVal)) yVal)
  have lhs₂ : Primrec lhs₂Fun :=
    (Primrec.nat_mul.comp yVal (Primrec.nat_add.comp (Primrec.const 1) yVal))
  have rhs₂ : Primrec rhs₂Fun :=
    (Primrec.nat_add.comp z₂Val z₂Val)
  have hEq₁ : PrimrecPred fun p : H10UPC × List Nat => lhs₁Fun p = z₁ValFun p :=
    Primrec.eq.comp lhs₁ z₁Val
  have hEq₂ : PrimrecPred fun p : H10UPC × List Nat => lhs₂Fun p = rhs₂Fun p :=
    Primrec.eq.comp lhs₂ rhs₂
  refine PrimrecRel.of_eq ((PrimrecPred.and hEq₁ hEq₂).primrecRel) ?_
  intro c vals
  cases c
  rfl

private theorem listWitness_primrecRel :
    PrimrecRel fun (cs : List H10UPC) (vals : List Nat) => listWitness cs vals := by
  refine PrimrecRel.of_eq h10upcSem_primrecRel.forall_mem_list ?_
  intro cs vals
  exact (listWitness_iff_forall_mem cs vals).symm

private theorem witnessStep_primrec :
    Primrec₂ fun (cs : List H10UPC) (vals : List Nat) =>
      if listWitness cs vals then some 0 else none := by
  let step : List H10UPC × List Nat → Option Nat :=
    fun p => if listWitness p.1 p.2 then some 0 else none
  have hPred : PrimrecPred fun p : List H10UPC × List Nat => listWitness p.1 p.2 := by
    exact listWitness_primrecRel
  have hstep : Primrec step := by
    exact Primrec.ite hPred (Primrec.const (some 0)) (Primrec.const none)
  exact hstep.to₂

private theorem searchStep_primrec :
    Primrec₂ fun cs n =>
      if listWitness cs (Denumerable.ofNat (List Nat) n)
      then (some 0 : Option Nat)
      else (none : Option Nat) := by
  let step : List H10UPC × Nat → Option Nat :=
    fun p =>
      if listWitness p.1 (Denumerable.ofNat (List Nat) p.2)
      then (some 0 : Option Nat)
      else (none : Option Nat)
  have hPred : PrimrecPred fun p : List H10UPC × Nat =>
      listWitness p.1 (Denumerable.ofNat (List Nat) p.2) := by
    exact PrimrecRel.comp listWitness_primrecRel Primrec.fst ((Primrec.ofNat (List Nat)).comp Primrec.snd)
  have hstep : Primrec step := by
    exact Primrec.ite hPred (Primrec.const (some 0)) (Primrec.const none)
  exact hstep.to₂

private def h10upcSearch : List H10UPC →. Nat :=
  fun cs =>
    Nat.rfindOpt fun n =>
      if listWitness cs (Denumerable.ofNat (List Nat) n)
      then (some 0 : Option Nat)
      else (none : Option Nat)

private theorem h10upcSearch_dom_iff (cs : List H10UPC) :
    (h10upcSearch cs).Dom ↔ ∃ vals : List Nat, listWitness cs vals := by
  unfold h10upcSearch
  constructor
  · intro h
    rcases Nat.rfindOpt_dom.1 h with ⟨n, u, hu⟩
    refine ⟨Denumerable.ofNat (List Nat) n, ?_⟩
    by_cases hw : listWitness cs (Denumerable.ofNat (List Nat) n)
    · exact hw
    · simp [hw] at hu
  · rintro ⟨vals, hvals⟩
    refine Nat.rfindOpt_dom.2 ⟨Encodable.encode vals, 0, ?_⟩
    simpa [Denumerable.ofNat_encode] using hvals

theorem h10upcSat_re : REPred H10UPCSat := by
  let f : List H10UPC →. Nat := fun cs =>
    Nat.rfindOpt fun n =>
      if listWitness cs (Denumerable.ofNat (List Nat) n)
      then (some 0 : Option Nat)
      else (none : Option Nat)
  have hsearch : Partrec f := by
    exact Partrec.rfindOpt searchStep_primrec.to_comp
  refine REPred.of_eq (Partrec.dom_re hsearch) ?_
  intro cs
  simpa [f, h10upcSearch] using
    (h10upcSearch_dom_iff cs).trans (h10upcSat_iff_exists_listWitness cs).symm

theorem h10upcSat_compl_not_re_of_not_computable
    (hcomplComp : ¬ ComputablePred (fun cs => ¬ H10UPCSat cs)) :
    ¬ REPred (fun cs => ¬ H10UPCSat cs) :=
  not_re_of_not_computable_of_re_compl
    hcomplComp
    (REPred.of_eq h10upcSat_re (fun cs => by simp))

end InqBQ
end HeytingLean
