import HeytingLean.LeanCP.RealWorld.BarrettReduceVerified
import HeytingLean.Crypto.Lattice.NTTIterative
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.Crypto.Lattice

namespace NTTVerified

abbrev q : Nat := NTTIterative.q
abbrev F : Type := NTTIterative.F
abbrev ForwardOp : Type := NTTIterative.ForwardOp

/-- The centered coefficient band for ML-KEM representatives. -/
def centeredBound : Int := 1664

/-- Worst-case centered product magnitude when both operands lie in the ML-KEM band. -/
def mulIntermediateBound : Int := centeredBound * centeredBound

/-- Worst-case centered butterfly numerator magnitude before normalization. -/
def butterflyIntermediateBound : Int := centeredBound + mulIntermediateBound

/-- Map an Int coefficient into the ML-KEM field. -/
def coeffToField (x : Int) : F := x

/-- Centered field representative, normalized once more through Barrett. -/
def normalizeFieldCoeff (x : F) : Int :=
  barrettReduceInt x.valMinAbs

theorem centeredBound_nonneg : 0 ≤ centeredBound := by
  native_decide

theorem mulIntermediateBound_nonneg : 0 ≤ mulIntermediateBound := by
  native_decide

theorem butterflyIntermediateBound_nonneg : 0 ≤ butterflyIntermediateBound := by
  native_decide

theorem mulIntermediateBound_lt_int32 :
    mulIntermediateBound < Int.ofNat (uintModulus .I32) := by
  native_decide

theorem butterflyIntermediateBound_lt_int32 :
    butterflyIntermediateBound < Int.ofNat (uintModulus .I32) := by
  native_decide

theorem valMinAbs_centered (x : F) :
    -centeredBound ≤ x.valMinAbs ∧ x.valMinAbs ≤ centeredBound := by
  have hnat : x.valMinAbs.natAbs ≤ 1664 := by
    simpa [q] using (ZMod.natAbs_valMinAbs_le (n := q) x)
  have habs : |x.valMinAbs| ≤ centeredBound := by
    rcases Int.natAbs_eq x.valMinAbs with h | h
    · rw [h]
      have hnatInt : ((x.valMinAbs.natAbs : Int) ≤ 1664) := by
        exact_mod_cast hnat
      simpa [centeredBound, abs_of_nonneg] using hnatInt
    · rw [h]
      have hnatInt : ((x.valMinAbs.natAbs : Int) ≤ 1664) := by
        exact_mod_cast hnat
      simpa [centeredBound, abs_of_nonneg] using hnatInt
  exact abs_le.mp habs

theorem normalizeFieldCoeff_eq_valMinAbs (x : F) :
    normalizeFieldCoeff x = x.valMinAbs := by
  have ⟨hl, hu⟩ := valMinAbs_centered x
  simpa [normalizeFieldCoeff] using
    barrettReduce_eq_self_of_abs_le_center x.valMinAbs hl hu

theorem coeffToField_normalizeFieldCoeff (x : F) :
    coeffToField (normalizeFieldCoeff x) = x := by
  rw [normalizeFieldCoeff_eq_valMinAbs]
  simpa [coeffToField] using (ZMod.coe_valMinAbs x)

theorem normalizeFieldCoeff_centered (x : F) :
    -centeredBound ≤ normalizeFieldCoeff x ∧ normalizeFieldCoeff x ≤ centeredBound := by
  simpa [normalizeFieldCoeff_eq_valMinAbs] using valMinAbs_centered x

/-- The machine-level twiddle representative attached to a lattice forward op. -/
def storedTwiddle (op : ForwardOp) : Int :=
  normalizeFieldCoeff op.zk

theorem storedTwiddle_centered (op : ForwardOp) :
    -centeredBound ≤ storedTwiddle op ∧ storedTwiddle op ≤ centeredBound := by
  simpa [storedTwiddle] using normalizeFieldCoeff_centered op.zk

theorem coeffToField_storedTwiddle (op : ForwardOp) :
    coeffToField (storedTwiddle op) = op.zk := by
  simpa [storedTwiddle] using coeffToField_normalizeFieldCoeff op.zk

/-- Convert an Int array into a size-256 field array by pointwise casting. -/
def fieldArray256 (a : Array Int) : Array F :=
  Array.ofFn (fun i : Fin 256 => coeffToField (a.getD i.val 0))

theorem fieldArray256_size (a : Array Int) : (fieldArray256 a).size = 256 := by
  simp [fieldArray256]

/-- Barrett-normalized butterfly on centered field representatives. -/
def butterflyStore (a b : Int) (zk : F) : Int × Int :=
  let u : F := coeffToField a + zk * coeffToField b
  let v : F := coeffToField a - zk * coeffToField b
  (normalizeFieldCoeff u, normalizeFieldCoeff v)

theorem coeffToField_butterflyStore_fst (a b : Int) (zk : F) :
    coeffToField (butterflyStore a b zk).1 = coeffToField a + zk * coeffToField b := by
  simp [butterflyStore, coeffToField_normalizeFieldCoeff]

theorem coeffToField_butterflyStore_snd (a b : Int) (zk : F) :
    coeffToField (butterflyStore a b zk).2 = coeffToField a - zk * coeffToField b := by
  simp [butterflyStore, coeffToField_normalizeFieldCoeff]

theorem butterflyStore_centered_fst (a b : Int) (zk : F) :
    -centeredBound ≤ (butterflyStore a b zk).1 ∧ (butterflyStore a b zk).1 ≤ centeredBound := by
  simpa [butterflyStore] using normalizeFieldCoeff_centered (coeffToField a + zk * coeffToField b)

theorem butterflyStore_centered_snd (a b : Int) (zk : F) :
    -centeredBound ≤ (butterflyStore a b zk).2 ∧ (butterflyStore a b zk).2 ≤ centeredBound := by
  simpa [butterflyStore] using normalizeFieldCoeff_centered (coeffToField a - zk * coeffToField b)

/-- Apply one forward NTT butterfly step to an Int array. -/
def applyForwardOpInt (a : Array Int) (op : ForwardOp) : Array Int :=
  let i1 := op.i1.val
  let i2 := op.i2.val
  let aj := a.getD i1 0
  let bj := a.getD i2 0
  let out := butterflyStore aj bj op.zk
  let a := a.setIfInBounds i2 out.2
  a.setIfInBounds i1 out.1

def applyForwardOpsInt (ops : List ForwardOp) (a : Array Int) : Array Int :=
  ops.foldl (fun acc op => applyForwardOpInt acc op) a

private theorem applyForwardOpInt_get_i2
    (a : Array Int) (ha : a.size = 256) (op : ForwardOp) (h12 : op.i1.val ≠ op.i2.val) :
    (applyForwardOpInt a op).getD op.i2.val 0 =
      (butterflyStore (a.getD op.i1.val 0) (a.getD op.i2.val 0) op.zk).2 := by
  have hi1 : op.i1.val < a.size := by
    simpa [ha] using op.i1.isLt
  have hi2 : op.i2.val < a.size := by
    simpa [ha] using op.i2.isLt
  let out := butterflyStore (a.getD op.i1.val 0) (a.getD op.i2.val 0) op.zk
  have hopt :
      (applyForwardOpInt a op)[op.i2.val]? = some out.2 := by
    simp [applyForwardOpInt, hi1, hi2, out, h12]
  rw [Array.getD_eq_getD_getElem?, hopt]
  simp [out]

private theorem applyForwardOpInt_get_unchanged
    (a : Array Int) (ha : a.size = 256) (op : ForwardOp) {i : Nat}
    (h1 : i ≠ op.i1.val) (h2 : i ≠ op.i2.val) :
    (applyForwardOpInt a op).getD i 0 = a.getD i 0 := by
  have hi1 : op.i1.val < a.size := by
    simpa [ha] using op.i1.isLt
  have hi2 : op.i2.val < a.size := by
    simpa [ha] using op.i2.isLt
  let out := butterflyStore (a.getD op.i1.val 0) (a.getD op.i2.val 0) op.zk
  by_cases hi : i < a.size
  · have hii : op.i2.val ≠ i := by
      intro h
      exact h2 h.symm
    have hii1 : op.i1.val ≠ i := by
      intro h
      exact h1 h.symm
    have hopt : (applyForwardOpInt a op)[i]? = a[i]? := by
      simp [applyForwardOpInt, hi1, hi2, out, hii, hii1]
    rw [Array.getD_eq_getD_getElem?, hopt, Array.getD_eq_getD_getElem?]
  · have hiFinal : ¬ i < (applyForwardOpInt a op).size := by
      simpa [applyForwardOpInt, Array.size_setIfInBounds, ha] using hi
    simp [Array.getD_eq_getD_getElem?, hi, hiFinal]

private theorem applyForwardOpField_get_i2
    (fa : Array F) (ha : fa.size = 256) (op : ForwardOp) (h12 : op.i1.val ≠ op.i2.val) :
    (NTTIterative.applyForwardOp fa op).getD op.i2.val 0 =
      fa.getD op.i1.val 0 - op.zk * fa.getD op.i2.val 0 := by
  have hi1 : op.i1.val < fa.size := by
    simpa [ha] using op.i1.isLt
  have hi2 : op.i2.val < fa.size := by
    simpa [ha] using op.i2.isLt
  let out2 := fa.getD op.i1.val 0 - op.zk * fa.getD op.i2.val 0
  let out1 := fa.getD op.i1.val 0 + op.zk * fa.getD op.i2.val 0
  have hopt :
      (NTTIterative.applyForwardOp fa op)[op.i2.val]? = some out2 := by
    simp [NTTIterative.applyForwardOp, hi1, hi2, out1, out2, h12]
  rw [Array.getD_eq_getD_getElem?, hopt]
  simp [out2]

private theorem applyForwardOpField_get_unchanged
    (fa : Array F) (ha : fa.size = 256) (op : ForwardOp) {i : Nat}
    (h1 : i ≠ op.i1.val) (h2 : i ≠ op.i2.val) :
    (NTTIterative.applyForwardOp fa op).getD i 0 = fa.getD i 0 := by
  have hi1 : op.i1.val < fa.size := by
    simpa [ha] using op.i1.isLt
  have hi2 : op.i2.val < fa.size := by
    simpa [ha] using op.i2.isLt
  by_cases hi : i < fa.size
  · have hii : op.i2.val ≠ i := by
      intro h
      exact h2 h.symm
    have hii1 : op.i1.val ≠ i := by
      intro h
      exact h1 h.symm
    let out2 := fa.getD op.i1.val 0 - op.zk * fa.getD op.i2.val 0
    let out1 := fa.getD op.i1.val 0 + op.zk * fa.getD op.i2.val 0
    have hopt : (NTTIterative.applyForwardOp fa op)[i]? = fa[i]? := by
      simp [NTTIterative.applyForwardOp, hi1, hi2, out1, out2, hii, hii1]
    rw [Array.getD_eq_getD_getElem?, hopt, Array.getD_eq_getD_getElem?]
  · have hiFinal : ¬ i < (NTTIterative.applyForwardOp fa op).size := by
      simpa [NTTIterative.applyForwardOp, Array.size_setIfInBounds, ha] using hi
    simp [Array.getD_eq_getD_getElem?, hi, hiFinal]

/-- The LeanCP-facing forward NTT schedule over 256 coefficients. -/
def nttIterativeInt (a : Array Int) (_ha : a.size = 256) : Array Int :=
  applyForwardOpsInt NTTIterative.forwardOps a

theorem forwardOp_indices_in_bounds (op : ForwardOp) :
    op.i1.val < 256 ∧ op.i2.val < 256 := by
  exact ⟨op.i1.isLt, op.i2.isLt⟩

private theorem fieldArray256_applyForwardOpInt
    (a : Array Int) (ha : a.size = 256) (op : ForwardOp) :
    fieldArray256 (applyForwardOpInt a op) =
      NTTIterative.applyForwardOp (fieldArray256 a) op := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 256
  · have hiL : i < (fieldArray256 (applyForwardOpInt a op)).size := by
      simpa [fieldArray256] using hi
    have hiR : i < (NTTIterative.applyForwardOp (fieldArray256 a) op).size := by
      simpa [fieldArray256, NTTIterative.applyForwardOp] using hi
    have hi1 : op.i1.val < a.size := by
      simpa [ha] using op.i1.isLt
    have hi2 : op.i2.val < a.size := by
      simpa [ha] using op.i2.isLt
    by_cases h1 : i = op.i1.val
    · subst h1
      simp [fieldArray256, applyForwardOpInt, NTTIterative.applyForwardOp, butterflyStore,
        coeffToField_normalizeFieldCoeff, Array.getD_eq_getD_getElem?, Array.size_setIfInBounds,
        Array.getElem?_ofFn, Array.getD_getElem?_setIfInBounds, hi, hi1, hi2,
        -Array.getElem?_eq_getElem]
    · by_cases h2 : i = op.i2.val
      · subst h2
        have h12 : op.i1.val ≠ op.i2.val := by
          intro h
          exact h1 h.symm
        have hleftGet := applyForwardOpInt_get_i2 a ha op h12
        have hrightGet := applyForwardOpField_get_i2 (fieldArray256 a) (fieldArray256_size a) op h12
        have hEq :
            coeffToField ((applyForwardOpInt a op).getD op.i2.val 0) =
              (NTTIterative.applyForwardOp (fieldArray256 a) op).getD op.i2.val 0 := by
          rw [hleftGet, hrightGet, coeffToField_butterflyStore_snd]
          simp [fieldArray256, Array.getD_eq_getD_getElem?, hi1, hi2]
        have hLopt :
            (fieldArray256 (applyForwardOpInt a op))[op.i2.val]? =
              some (coeffToField ((applyForwardOpInt a op).getD op.i2.val 0)) := by
          simp [fieldArray256, Array.getD_eq_getD_getElem?, hiL]
        have hRopt :
            (NTTIterative.applyForwardOp (fieldArray256 a) op)[op.i2.val]? =
              some ((NTTIterative.applyForwardOp (fieldArray256 a) op).getD op.i2.val 0) := by
          simp [Array.getD_eq_getD_getElem?, hiR]
        rw [hLopt, hRopt]
        exact congrArg some hEq
      · have hleftGet := applyForwardOpInt_get_unchanged a ha op h1 h2
        have hrightGet := applyForwardOpField_get_unchanged (fieldArray256 a) (fieldArray256_size a) op h1 h2
        have hEq :
            coeffToField ((applyForwardOpInt a op).getD i 0) =
              (NTTIterative.applyForwardOp (fieldArray256 a) op).getD i 0 := by
          rw [hleftGet, hrightGet]
          simp [fieldArray256, Array.getD_eq_getD_getElem?, hi]
        have hLopt :
            (fieldArray256 (applyForwardOpInt a op))[i]? =
              some (coeffToField ((applyForwardOpInt a op).getD i 0)) := by
          simp [fieldArray256, Array.getD_eq_getD_getElem?, hi]
        have hRopt :
            (NTTIterative.applyForwardOp (fieldArray256 a) op)[i]? =
              some ((NTTIterative.applyForwardOp (fieldArray256 a) op).getD i 0) := by
          simp [Array.getD_eq_getD_getElem?, hiR]
        rw [hLopt, hRopt]
        exact congrArg some hEq
  · simp [fieldArray256, NTTIterative.applyForwardOp, applyForwardOpInt, Array.getElem?_ofFn, hi]

private theorem fieldArray256_applyForwardOpsInt
    (ops : List ForwardOp) (a : Array Int) (ha : a.size = 256) :
    fieldArray256 (applyForwardOpsInt ops a) =
      NTTIterative.applyForwardOps ops (fieldArray256 a) := by
  revert a
  induction ops with
  | nil =>
      intro a ha
      simp [applyForwardOpsInt, NTTIterative.applyForwardOps]
  | cons op ops ih =>
      intro a ha
      have ha' : (applyForwardOpInt a op).size = 256 := by
        simp [applyForwardOpInt, ha]
      calc
        fieldArray256 (applyForwardOpsInt (op :: ops) a)
            = fieldArray256 (applyForwardOpsInt ops (applyForwardOpInt a op)) := by
                simp [applyForwardOpsInt]
        _ = NTTIterative.applyForwardOps ops (fieldArray256 (applyForwardOpInt a op)) := ih _ ha'
        _ = NTTIterative.applyForwardOps ops (NTTIterative.applyForwardOp (fieldArray256 a) op) := by
              rw [fieldArray256_applyForwardOpInt a ha op]
        _ = NTTIterative.applyForwardOps (op :: ops) (fieldArray256 a) := by
              simp [NTTIterative.applyForwardOps]

theorem size_applyForwardOpInt (a : Array Int) (op : ForwardOp) :
    (applyForwardOpInt a op).size = a.size := by
  simp [applyForwardOpInt]

theorem size_applyForwardOpsInt (ops : List ForwardOp) (a : Array Int) :
    (applyForwardOpsInt ops a).size = a.size := by
  revert a
  induction ops with
  | nil =>
      intro a
      simp [applyForwardOpsInt]
  | cons op ops ih =>
      intro a
      calc
        (applyForwardOpsInt (op :: ops) a).size
            = (applyForwardOpsInt ops (applyForwardOpInt a op)).size := by
                simp [applyForwardOpsInt]
        _ = (applyForwardOpInt a op).size := ih _
        _ = a.size := size_applyForwardOpInt a op

theorem size_nttIterativeInt (a : Array Int) (ha : a.size = 256) :
    (nttIterativeInt a ha).size = 256 := by
  simpa [nttIterativeInt, ha] using size_applyForwardOpsInt NTTIterative.forwardOps a

/-- Centered-band invariant for stored machine coefficients. -/
def CenteredCoeffs (a : Array Int) : Prop :=
  ∀ i, i < a.size → -centeredBound ≤ a.getD i 0 ∧ a.getD i 0 ≤ centeredBound

theorem centered_applyForwardOpInt (a : Array Int) (ha : a.size = 256) (op : ForwardOp) :
    CenteredCoeffs a → CenteredCoeffs (applyForwardOpInt a op) := by
  intro hCentered
  intro i hi
  have hi1 : op.i1.val < a.size := by
    simpa [ha] using op.i1.isLt
  have hi2 : op.i2.val < a.size := by
    simpa [ha] using op.i2.isLt
  by_cases h1 : i = op.i1.val
  · subst h1
    simpa [applyForwardOpInt, Array.getD_eq_getD_getElem?, Array.getD_getElem?_setIfInBounds,
      hi1, hi2, -Array.getElem?_eq_getElem]
      using butterflyStore_centered_fst (a.getD op.i1.val 0) (a.getD op.i2.val 0) op.zk
  · by_cases h2 : i = op.i2.val
    · subst h2
      have h12 : op.i1.val ≠ op.i2.val := by
        intro h
        exact h1 h.symm
      rw [applyForwardOpInt_get_i2 a ha op h12]
      exact butterflyStore_centered_snd (a.getD op.i1.val 0) (a.getD op.i2.val 0) op.zk
    · have hsize : (applyForwardOpInt a op).size = a.size := size_applyForwardOpInt a op
      have hlt : i < a.size := by
        simpa [hsize] using hi
      rcases hCentered i hlt with ⟨hl, hu⟩
      rw [applyForwardOpInt_get_unchanged a ha op h1 h2]
      exact And.intro hl hu

theorem centered_applyForwardOpsInt (ops : List ForwardOp) (a : Array Int) (ha : a.size = 256) :
    CenteredCoeffs a → CenteredCoeffs (applyForwardOpsInt ops a) := by
  intro h
  revert a ha h
  induction ops with
  | nil =>
      intro a ha h
      simpa [applyForwardOpsInt] using h
  | cons op ops ih =>
      intro a ha h
      have hStep : CenteredCoeffs (applyForwardOpInt a op) :=
        centered_applyForwardOpInt a ha op h
      have ha' : (applyForwardOpInt a op).size = 256 := by
        simpa [ha] using size_applyForwardOpInt a op
      simpa [applyForwardOpsInt] using ih (applyForwardOpInt a op) ha' hStep

theorem centered_nttIterativeInt (a : Array Int) (ha : a.size = 256) :
    CenteredCoeffs a → CenteredCoeffs (nttIterativeInt a ha) := by
  simpa [nttIterativeInt] using centered_applyForwardOpsInt NTTIterative.forwardOps a ha

theorem butterfly_raw_intermediates_safe (a b : Int) (op : ForwardOp)
    (ha : -centeredBound ≤ a ∧ a ≤ centeredBound)
    (hb : -centeredBound ≤ b ∧ b ≤ centeredBound) :
    |storedTwiddle op * b| ≤ mulIntermediateBound ∧
      |a + storedTwiddle op * b| ≤ butterflyIntermediateBound ∧
      |a - storedTwiddle op * b| ≤ butterflyIntermediateBound := by
  have hza : |a| ≤ centeredBound := abs_le.mpr ha
  have hzb : |b| ≤ centeredBound := abs_le.mpr hb
  have hzk : |storedTwiddle op| ≤ centeredBound := abs_le.mpr (storedTwiddle_centered op)
  let t := storedTwiddle op * b
  have hprodAbs : |t| ≤ mulIntermediateBound := by
    calc
      |t| = |storedTwiddle op| * |b| := by
        simp [t, abs_mul]
      _ ≤ centeredBound * centeredBound := by
        have hcb : 0 ≤ centeredBound := centeredBound_nonneg
        gcongr
      _ = mulIntermediateBound := by
        simp [mulIntermediateBound]
  have hsumAbs : |a + t| ≤ butterflyIntermediateBound := by
    calc
      |a + t| = |a - (-t)| := by
        simp [sub_eq_add_neg, add_comm]
      _ ≤ |a - 0| + |0 - (-t)| := abs_sub_le a 0 (-t)
      _ = |a| + |t| := by
        simp
      _ ≤ centeredBound + mulIntermediateBound := by
        gcongr
      _ = butterflyIntermediateBound := by
        simp [butterflyIntermediateBound]
  have hsubAbs : |a - t| ≤ butterflyIntermediateBound := by
    calc
      |a - t| ≤ |a - 0| + |0 - t| := abs_sub_le a 0 t
      _ = |a| + |t| := by
        simp
      _ ≤ centeredBound + mulIntermediateBound := by
        gcongr
      _ = butterflyIntermediateBound := by
        simp [butterflyIntermediateBound]
  simpa [t] using And.intro hprodAbs (And.intro hsumAbs hsubAbs)

theorem butterfly_step_safe (a : Array Int) (ha : a.size = 256) (op : ForwardOp)
    (hCentered : CenteredCoeffs a) :
    |storedTwiddle op * a.getD op.i2.val 0| ≤ mulIntermediateBound ∧
      |a.getD op.i1.val 0 + storedTwiddle op * a.getD op.i2.val 0| ≤ butterflyIntermediateBound ∧
      |a.getD op.i1.val 0 - storedTwiddle op * a.getD op.i2.val 0| ≤ butterflyIntermediateBound := by
  have hi1 : op.i1.val < a.size := by
    simpa [ha] using op.i1.isLt
  have hi2 : op.i2.val < a.size := by
    simpa [ha] using op.i2.isLt
  have h1 := hCentered op.i1.val hi1
  have h2 := hCentered op.i2.val hi2
  simpa using butterfly_raw_intermediates_safe (a.getD op.i1.val 0) (a.getD op.i2.val 0) op h1 h2

theorem butterfly_step_lt_int32 (a : Array Int) (ha : a.size = 256) (op : ForwardOp)
    (hCentered : CenteredCoeffs a) :
    |storedTwiddle op * a.getD op.i2.val 0| < Int.ofNat (uintModulus .I32) ∧
      |a.getD op.i1.val 0 + storedTwiddle op * a.getD op.i2.val 0| < Int.ofNat (uintModulus .I32) ∧
      |a.getD op.i1.val 0 - storedTwiddle op * a.getD op.i2.val 0| < Int.ofNat (uintModulus .I32) := by
  rcases butterfly_step_safe a ha op hCentered with ⟨hprod, hsum, hsub⟩
  exact ⟨lt_of_le_of_lt hprod mulIntermediateBound_lt_int32,
    lt_of_le_of_lt hsum butterflyIntermediateBound_lt_int32,
    lt_of_le_of_lt hsub butterflyIntermediateBound_lt_int32⟩

theorem nttIterativeInt_refines (a : Array Int) (ha : a.size = 256) :
    fieldArray256 (nttIterativeInt a ha) =
      NTTIterative.nttIterative (fieldArray256 a) (fieldArray256_size a) := by
  simpa [nttIterativeInt, NTTIterative.nttIterative] using
    fieldArray256_applyForwardOpsInt NTTIterative.forwardOps a ha

end NTTVerified

end HeytingLean.LeanCP.RealWorld
