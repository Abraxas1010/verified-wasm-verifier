import HeytingLean.Numbers.Surreal.Equiv
import HeytingLean.Numbers.Surreal.QuotOps
import HeytingLean.Numbers.Surreal.QuotCoreSemantics
import HeytingLean.Numbers.Surreal.Embeddings
import HeytingLean.Numbers.Surreal.Instances
import HeytingLean.Numbers.Surreal.OrderNormalized

open HeytingLean
open HeytingLean.Numbers
open HeytingLean.Numbers.Surreal

/-! Smoke tests for quotient-level Surreal operations and embeddings. -/

#check Surreal.zeroQ
#check Surreal.addQ
#check Surreal.negQ
#check Surreal.mulQ

noncomputable section
  variable (x y z : Surreal.SurrealQ)

  example : Surreal.canonicalizeQ (Surreal.ofGameQ (Surreal.repr x)) =
      Surreal.ofGameQ (Surreal.repr x) := by
    exact Surreal.canonicalizeQ_ofGame (Surreal.repr x)

  example : Surreal.canonicalizeQ Surreal.zeroQ = Surreal.zeroQ := by
    exact Surreal.canonicalizeQ_zeroQ

  example : Surreal.canonicalizeQ (Surreal.addQ x y) = Surreal.addQ x y := by
    exact Surreal.canonicalizeQ_addQ x y

  example : Surreal.canonicalizeQ (Surreal.negQ x) = Surreal.negQ x := by
    exact Surreal.canonicalizeQ_negQ x

  example : Surreal.canonicalizeQ (Surreal.mulQ x y) = Surreal.mulQ x y := by
    exact Surreal.canonicalizeQ_mulQ x y

  example : Surreal.canonicalizeQ (Surreal.normalizeQ x) = Surreal.normalizeQ x := by
    exact Surreal.canonicalizeQ_normalizeQ x

  example : Surreal.canonicalizeQ (Surreal.canonicalizeQ x) = Surreal.canonicalizeQ x := by
    exact Surreal.canonicalizeQ_idem x

  example : Surreal.zeroQ = Surreal.zeroQCore := by
    exact Surreal.zeroQ_eq_zeroQCore

  example : Surreal.addQ x y = Surreal.addQCore x y := by
    exact Surreal.addQ_eq_addQCore x y

  example : Surreal.negQ x = Surreal.negQCore x := by
    exact Surreal.negQ_eq_negQCore x

  example : Surreal.mulQ x y = Surreal.mulQCore x y := by
    exact Surreal.mulQ_eq_mulQCore x y

  example :
      Surreal.toIGameQ (Surreal.addQ x y) = Surreal.toIGameQ x + Surreal.toIGameQ y := by
    exact Surreal.toIGameQ_addQ x y

  example :
      Surreal.toIGameQ (Surreal.negQ x) = -Surreal.toIGameQ x := by
    exact Surreal.toIGameQ_negQ x

  example :
      Surreal.toIGameQ (Surreal.mulQ x y) = Surreal.toIGameQ x * Surreal.toIGameQ y := by
    exact Surreal.toIGameQ_mulQ x y

  example :
      Surreal.toIGameQ Surreal.zeroQ = 0 := by
    exact Surreal.toIGameQ_zeroQ

  example :
      Surreal.toIGameQ (Surreal.mulQ Surreal.zeroQ x) = 0 := by
    exact Surreal.toIGameQ_mul_zeroQ_left x

  example :
      Surreal.toIGameQ (Surreal.mulQ x Surreal.zeroQ) = 0 := by
    exact Surreal.toIGameQ_mul_zeroQ_right x

  example :
      Surreal.toIGameQ (Surreal.addQ Surreal.zeroQ x) = Surreal.toIGameQ x := by
    exact Surreal.toIGameQ_add_zeroQ_left x

  example :
      Surreal.toIGameQ (Surreal.addQ x Surreal.zeroQ) = Surreal.toIGameQ x := by
    exact Surreal.toIGameQ_add_zeroQ_right x

  example :
      Surreal.toIGameQ (Surreal.mulQ x (Surreal.addQ y z)) ≈
        Surreal.toIGameQ (Surreal.addQ (Surreal.mulQ x y) (Surreal.mulQ x z)) := by
    exact Surreal.toIGameQ_mul_addQ_equiv x y z

  example :
      Surreal.toIGameQ (Surreal.mulQ (Surreal.addQ x y) z) ≈
        Surreal.toIGameQ (Surreal.addQ (Surreal.mulQ x z) (Surreal.mulQ y z)) := by
    exact Surreal.toIGameQ_add_mulQ_equiv x y z

  example :
      Surreal.toIGameQ (Surreal.mulQ (Surreal.mulQ x y) z) ≈
        Surreal.toIGameQ (Surreal.mulQ x (Surreal.mulQ y z)) := by
    exact Surreal.toIGameQ_mulQ_assoc_equiv x y z

  example :
      Surreal.toIGameQ (Surreal.mulQ x y) = Surreal.toIGameQ (Surreal.mulQ y x) := by
    exact Surreal.toIGameQ_mulQ_comm x y

  example :
      Surreal.toIGameQ (Surreal.addQ x y) = Surreal.toIGameQ (Surreal.addQ y x) := by
    exact Surreal.toIGameQ_addQ_comm x y

  example :
      Surreal.toIGameQ (Surreal.addQ (Surreal.addQ x y) z) =
        Surreal.toIGameQ (Surreal.addQ x (Surreal.addQ y z)) := by
    exact Surreal.toIGameQ_addQ_assoc x y z

  example :
      Surreal.toIGameQ (Surreal.addQ (Surreal.negQ x) x) ≈ 0 := by
    exact Surreal.toIGameQ_add_left_negQ_equiv_zero x

  example :
      Surreal.toIGameQ (Surreal.addQ x (Surreal.negQ x)) ≈ 0 := by
    exact Surreal.toIGameQ_add_right_negQ_equiv_zero x

  example :
      Surreal.toIGameQ (Surreal.addQ (Surreal.negQ x) (Surreal.addQ x y)) ≈ Surreal.toIGameQ y := by
    exact Surreal.toIGameQ_add_left_cancelQ_equiv x y

  example :
      Surreal.toIGameQ (Surreal.addQ x (Surreal.addQ (Surreal.negQ x) y)) ≈ Surreal.toIGameQ y := by
    exact Surreal.toIGameQ_add_right_cancelQ_equiv x y
end

/-! Embeddings -/

#check Surreal.embedOrdinal

noncomputable section
  open HeytingLean.Numbers
  -- Simple dyadic embedding checks
  #check Surreal.Dyadic
  #check Surreal.ofDyadic
  example : Surreal.SurrealQ :=
    Surreal.ofDyadic { num := (Int.ofNat 3), pow := 1 }
  example :
      Surreal.ofDyadic { num := Int.ofNat 2, pow := 0 } = Surreal.embedOrdinal 2 := by
    exact Surreal.ofDyadic_pow_zero_ofNat 2
  example :
      Surreal.ofDyadic { num := Int.ofNat 2, pow := 2 } =
        Surreal.ofDyadic { num := Int.ofNat 1, pow := 1 } := by
    exact Surreal.ofDyadic_two_quarters_eq_one_half
  example : Surreal.ofDyadic { num := Int.ofNat 1, pow := 1 } =
      Quotient.mk (s := Surreal.approxSetoid)
        (HeytingLean.Numbers.SurrealCore.canonicalize Surreal.oneHalfPreGame) := by
    exact Surreal.ofDyadic_one_half_ref
  example (n : Int) (k : Nat) :
      Surreal.ofDyadic { num := 2 * n, pow := Nat.succ k } =
        Surreal.ofDyadic { num := n, pow := k } := by
    exact Surreal.ofDyadic_double_num_succ_pow n k
  example :
      Surreal.ofDyadic { num := (-2 : Int), pow := 1 } =
        Surreal.ofDyadic { num := (-1 : Int), pow := 0 } := by
    exact Surreal.ofDyadic_double_num_succ_pow (-1) 0
  #check Surreal.normalizeQ
  example (x : Surreal.SurrealQ) :
      Surreal.normalizeQ (Surreal.normalizeQ x) = Surreal.normalizeQ x := by
    exact Surreal.normalizeQ_idem x

/-! Numerals and operations via instances -/

#check (0 : Surreal.SurrealQ)
#check (1 : Surreal.SurrealQ)

noncomputable section
  variable (x : Surreal.SurrealQ)
  example : Surreal.SurrealQ := (2 : Surreal.SurrealQ) + 3
  example : Surreal.SurrealQ := (2 : Surreal.SurrealQ) * 0
  example : Surreal.SurrealQ := -x
  example : Surreal.canonicalizeQ (Surreal.addQ (0 : Surreal.SurrealQ) x) =
      Surreal.addQ (0 : Surreal.SurrealQ) x := by
    exact Surreal.canonicalizeQ_addQ (0 : Surreal.SurrealQ) x
end

/-! Normalized order checks -/

noncomputable section
  variable (x y z : Surreal.SurrealQ)
  #check Surreal.leNQ
  example : Surreal.leNQ x x := by
    exact Surreal.leNQ_refl x
  example (hxy : Surreal.leNQ x y) (hyz : Surreal.leNQ y z) :
      Surreal.leNQ x z := by
    exact Surreal.leNQ_trans (x:=x) (y:=y) (z:=z) hxy hyz
  example (hxy : Surreal.leNQ x y) (hyx : Surreal.leNQ y x) :
      Surreal.normalizeQ x = Surreal.normalizeQ y := by
    exact Surreal.leNQ_antisymm_norm (x:=x) (y:=y) hxy hyx
end
end
