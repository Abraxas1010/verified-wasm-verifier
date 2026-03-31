import HeytingLean.Moonshine.Borcherds.Replication
import HeytingLean.Moonshine.Monster.Construction

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine

/--
Gate-E output package: replication/genus-zero side data sufficient to recover the full
Moonshine statement witness.
-/
structure GenusZeroData where
  R : ReplicationData
  thompson_is_hauptmodul :
    ∀ g : R.D.B.C.S.M, ∃ H : HauptmodulData R.D.B.C.S.M, H.qExp = ThompsonSeries R.D.B.C.V g

namespace GenusZeroData

/-- Upgrade Gate-E genus-zero output into the Gate-D/full statement construction package. -/
def toMonsterConstructionData (G : GenusZeroData) : MonsterConstructionData where
  toMonsterConstructionCoreData := G.R.D.B.C
  thompson_is_hauptmodul := G.thompson_is_hauptmodul

/-- Any genus-zero package yields the Monstrous Moonshine headline statement. -/
theorem statement (G : GenusZeroData) : MonstrousMoonshineStatement G.R.D.B.C.S :=
  (G.toMonsterConstructionData).statement

/--
Gate-E identity-element coefficient bridge: the denominator-series output agrees with `J_q`
through the first Moonshine coefficients.
-/
theorem denominatorSeries_one_coeffs_match_J_q (G : GenusZeroData) :
    (G.R.D.denominatorSeries (1 : G.R.D.B.C.S.M)).coeff (-1) = Modular.J_q.coeff (-1) ∧
    (G.R.D.denominatorSeries (1 : G.R.D.B.C.S.M)).coeff 0 = Modular.J_q.coeff 0 ∧
    (G.R.D.denominatorSeries (1 : G.R.D.B.C.S.M)).coeff 1 = Modular.J_q.coeff 1 ∧
    (G.R.D.denominatorSeries (1 : G.R.D.B.C.S.M)).coeff 2 = Modular.J_q.coeff 2 :=
  G.R.D.denominatorSeries_one_coeffs_match_J_q

/--
Gate-E denominator→Hauptmodul bridge for an arbitrary element:
the genus-zero witness can be chosen to have `q`-expansion exactly the denominator series.
-/
theorem exists_hauptmodul_qExp_eq_denominatorSeries
    (G : GenusZeroData) (g : G.R.D.B.C.S.M) :
    ∃ H : HauptmodulData G.R.D.B.C.S.M, H.qExp = G.R.D.denominatorSeries g := by
  rcases G.thompson_is_hauptmodul g with ⟨H, hH⟩
  refine ⟨H, ?_⟩
  calc
    H.qExp = ThompsonSeries G.R.D.B.C.V g := hH
    _ = G.R.D.denominatorSeries g := (G.R.D.denominator_eq_thompson g).symm

/--
Identity-element specialization of `exists_hauptmodul_qExp_eq_denominatorSeries`.
-/
theorem exists_hauptmodul_one_qExp_eq_denominatorSeries
    (G : GenusZeroData) :
    ∃ H : HauptmodulData G.R.D.B.C.S.M,
      H.qExp = G.R.D.denominatorSeries (1 : G.R.D.B.C.S.M) :=
  G.exists_hauptmodul_qExp_eq_denominatorSeries (1 : G.R.D.B.C.S.M)

/--
Gate-E export: existence of a Hauptmodul witness for `g = 1` with first coefficients matching
`J_q`.
-/
theorem exists_hauptmodul_one_qExp_coeffs_match_J_q (G : GenusZeroData) :
    ∃ H : HauptmodulData G.R.D.B.C.S.M,
      H.qExp = ThompsonSeries G.R.D.B.C.V (1 : G.R.D.B.C.S.M) ∧
      H.qExp.coeff (-1) = Modular.J_q.coeff (-1) ∧
      H.qExp.coeff 0 = Modular.J_q.coeff 0 ∧
      H.qExp.coeff 1 = Modular.J_q.coeff 1 ∧
      H.qExp.coeff 2 = Modular.J_q.coeff 2 :=
  (G.toMonsterConstructionData).exists_hauptmodul_one_qExp_coeffs_match_J_q

/--
Identity-element denominator/Hauptmodul bridge with first coefficient checks against `J_q`.
-/
theorem exists_hauptmodul_one_qExp_eq_denominatorSeries_coeffs_match_J_q
    (G : GenusZeroData) :
    ∃ H : HauptmodulData G.R.D.B.C.S.M,
      H.qExp = G.R.D.denominatorSeries (1 : G.R.D.B.C.S.M) ∧
      H.qExp.coeff (-1) = Modular.J_q.coeff (-1) ∧
      H.qExp.coeff 0 = Modular.J_q.coeff 0 ∧
      H.qExp.coeff 1 = Modular.J_q.coeff 1 ∧
      H.qExp.coeff 2 = Modular.J_q.coeff 2 := by
  rcases G.exists_hauptmodul_one_qExp_eq_denominatorSeries with ⟨H, hH⟩
  refine ⟨H, hH, ?_⟩
  rcases G.denominatorSeries_one_coeffs_match_J_q with ⟨hneg1, h0, h1, h2⟩
  constructor
  · simpa [hH] using hneg1
  constructor
  · simpa [hH] using h0
  constructor
  · simpa [hH] using h1
  · simpa [hH] using h2

end GenusZeroData

end HeytingLean.Moonshine
