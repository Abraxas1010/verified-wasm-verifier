import HeytingLean.Genesis.CantorCutBridge
import HeytingLean.MirandaDynamics.Billiards.CantorEncoding
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# Genesis.CantorTopology

Topological Cantor-cut lane:
- continuity of prefix/tail transports,
- homeomorphism between prefix cylinders and full path space,
- transport hook into witness-interior stabilization checks.
-/

namespace HeytingLean.Genesis

open Cardinal

local instance (pre : List Bool) : TopologicalSpace (EvalPathFrom pre) := by
  unfold EvalPathFrom
  infer_instance

/-- Continuity of finite-prefix insertion on path space. -/
theorem continuous_withPrefix (pre : List Bool) : Continuous (withPrefix pre) := by
  refine continuous_pi ?_
  intro n
  by_cases h : n < pre.length
  · simpa [withPrefix, h] using
      (continuous_const : Continuous fun _ : EvalPath => pre.get ⟨n, h⟩)
  · simpa [withPrefix, h] using
      (continuous_apply (n - pre.length) : Continuous fun p : EvalPath => p (n - pre.length))

/-- Continuity of the canonical embedding into a fixed prefix cylinder. -/
theorem continuous_attachPrefix (pre : List Bool) : Continuous (attachPrefix pre) := by
  simpa [attachPrefix] using
    (continuous_withPrefix pre).subtype_mk (fun p => (attachPrefix pre p).2)

/-- Continuity of prefix dropping from a fixed cylinder back to full path space. -/
theorem continuous_dropPrefix (pre : List Bool) : Continuous (dropPrefix pre) := by
  refine continuous_pi ?_
  intro n
  simpa [dropPrefix] using
    ((continuous_apply (n + pre.length) : Continuous fun p : EvalPath => p (n + pre.length)).comp
      continuous_subtype_val)

/-- Topological self-similarity: every prefix cylinder is homeomorphic to the full path space. -/
noncomputable def evalPath_prefix_homeomorph (pre : List Bool) : EvalPathFrom pre ≃ₜ EvalPath where
  toEquiv := evalTreeSelfSimilar pre
  continuous_toFun := continuous_dropPrefix pre
  continuous_invFun := continuous_attachPrefix pre

/-- Canonical topological self-similarity alias. -/
noncomputable def evalPath_self_similar_homeomorph (pre : List Bool) : EvalPathFrom pre ≃ₜ EvalPath :=
  evalPath_prefix_homeomorph pre

@[simp] theorem evalPath_prefix_homeomorph_toFun (pre : List Bool) (p : EvalPathFrom pre) :
    evalPath_prefix_homeomorph pre p = dropPrefix pre p := rfl

@[simp] theorem evalPath_prefix_homeomorph_invFun (pre : List Bool) (p : EvalPath) :
    (evalPath_prefix_homeomorph pre).symm p = attachPrefix pre p := rfl

/-- Transport a prefixed path through the topological homeomorphism into witness interior. -/
def prefix_homeomorph_to_witnessInterior
    (pre : List Bool) (p : EvalPathFrom pre) (depth : Nat) : WitnessInterior :=
  cantorCut_to_witnessInterior (evalPath_prefix_homeomorph pre p) depth

/-- Homeomorphic transport preserves the head-bit stabilization classifier. -/
theorem cantorCut_homeomorph_transport_ready
    (pre : List Bool) (p : EvalPathFrom pre) (depth : Nat) :
    eventualStabilizes (prefix_homeomorph_to_witnessInterior pre p depth).source
      ↔ (evalPath_prefix_homeomorph pre p) 0 = true := by
  simpa [prefix_homeomorph_to_witnessInterior] using
    (cantorCut_transport_ready (p := evalPath_prefix_homeomorph pre p) (depth := depth))

/-- Canonical embedding of EvalPath into the ternary Cantor set coordinates. -/
noncomputable def evalPath_to_ternaryCantor (p : EvalPath) : ℝ :=
  HeytingLean.MirandaDynamics.Billiards.cantorEncode p

/-- Every EvalPath encodes to a point in the ternary Cantor set. -/
theorem evalPath_to_ternaryCantor_mem_cantorSet (p : EvalPath) :
    evalPath_to_ternaryCantor p ∈ cantorSet := by
  simpa [evalPath_to_ternaryCantor] using
    (HeytingLean.MirandaDynamics.Billiards.cantorEncode_mem_cantorSet p)

/-- The ternary Cantor encoding is injective on EvalPath. -/
theorem evalPath_to_ternaryCantor_injective : Function.Injective evalPath_to_ternaryCantor := by
  simpa [evalPath_to_ternaryCantor] using
    (HeytingLean.MirandaDynamics.Billiards.cantorEncode_injective :
      Function.Injective HeytingLean.MirandaDynamics.Billiards.cantorEncode)

/-- The canonical ternary Cantor encoding is continuous on path space. -/
theorem continuous_evalPath_to_ternaryCantor : Continuous evalPath_to_ternaryCantor := by
  change Continuous (fun p : EvalPath =>
    (2 / 3 : ℝ) * (∑' n : ℕ, Cardinal.cantorFunctionAux (1 / 3 : ℝ) p n))
  let u : ℕ → ℝ := fun n => (1 / 3 : ℝ) ^ n
  have hterm_cont :
      ∀ n : ℕ, Continuous (fun p : EvalPath => Cardinal.cantorFunctionAux (1 / 3 : ℝ) p n) := by
    intro n
    have hdisc : Continuous (fun b : Bool => cond b ((1 / 3 : ℝ) ^ n) 0) :=
      continuous_of_discreteTopology
    simpa [Cardinal.cantorFunctionAux] using hdisc.comp (continuous_apply n)
  have hsum_u : Summable u := by
    simpa [u] using
      (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 3 : ℝ))
        (by norm_num : (1 / 3 : ℝ) < 1))
  have hbound :
      ∀ n p, ‖Cardinal.cantorFunctionAux (1 / 3 : ℝ) p n‖ ≤ u n := by
    intro n p
    by_cases h : p n
    · simp [Cardinal.cantorFunctionAux, u, h, abs_of_nonneg (pow_nonneg (by norm_num) _)]
    · simp [Cardinal.cantorFunctionAux, u, h]
  have htsum :
      Continuous (fun p : EvalPath => ∑' n : ℕ, Cardinal.cantorFunctionAux (1 / 3 : ℝ) p n) :=
    continuous_tsum hterm_cont hsum_u hbound
  exact continuous_const.mul htsum

/-- View an EvalPath as a typed point of `cantorSet`. -/
noncomputable def evalPath_to_ternaryCantorSubtype (p : EvalPath) : {x : ℝ // x ∈ cantorSet} :=
  ⟨evalPath_to_ternaryCantor p, evalPath_to_ternaryCantor_mem_cantorSet p⟩

/-- The image of EvalPath under the ternary encoding is a subset of `cantorSet`. -/
theorem evalPath_to_ternaryCantor_range_subset :
    Set.range evalPath_to_ternaryCantor ⊆ cantorSet := by
  intro x hx
  rcases hx with ⟨p, rfl⟩
  exact evalPath_to_ternaryCantor_mem_cantorSet p

/-- Explicit subset-equivalence used by the Genesis Phase13+ Cantor bridge. -/
noncomputable def evalPath_equiv_ternaryCantor_range :
    EvalPath ≃ Set.range evalPath_to_ternaryCantor :=
  Equiv.ofInjective evalPath_to_ternaryCantor evalPath_to_ternaryCantor_injective

@[simp] theorem evalPath_equiv_ternaryCantor_range_apply (p : EvalPath) :
    (evalPath_equiv_ternaryCantor_range p).1 = evalPath_to_ternaryCantor p := rfl

/-- Glossary-level alias: CantorCutPath inherits the same subset-equivalence. -/
noncomputable def cantorCut_equiv_ternaryCantor_range :
    CantorCutPath ≃ Set.range evalPath_to_ternaryCantor :=
  evalPath_equiv_ternaryCantor_range

/-- Prefix-homeomorphic transport remains inside the ternary Cantor set image lane. -/
theorem prefix_homeomorph_image_mem_cantorSet (pre : List Bool) (p : EvalPathFrom pre) :
    evalPath_to_ternaryCantor (evalPath_prefix_homeomorph pre p) ∈ cantorSet :=
  evalPath_to_ternaryCantor_mem_cantorSet (evalPath_prefix_homeomorph pre p)

/-- The typed Cantor embedding is injective. -/
theorem evalPath_to_ternaryCantorSubtype_injective :
    Function.Injective evalPath_to_ternaryCantorSubtype := by
  intro p q h
  apply evalPath_to_ternaryCantor_injective
  exact congrArg Subtype.val h

/-- The typed Cantor embedding is continuous. -/
theorem continuous_evalPath_to_ternaryCantorSubtype :
    Continuous evalPath_to_ternaryCantorSubtype := by
  exact continuous_evalPath_to_ternaryCantor.subtype_mk
    (fun p => evalPath_to_ternaryCantor_mem_cantorSet p)

/-- Topological upgrade: the concrete encoding is a homeomorphism onto its range. -/
noncomputable def evalPath_to_ternaryCantor_homeomorph_range :
    EvalPath ≃ₜ Set.range evalPath_to_ternaryCantor :=
  (continuous_evalPath_to_ternaryCantor.isClosedEmbedding
      evalPath_to_ternaryCantor_injective).isEmbedding.toHomeomorph

private theorem cantorSet_step_exists (x : {x : ℝ // x ∈ cantorSet}) :
    ∃ p : Bool × {y : ℝ // y ∈ cantorSet},
      x.1 = if p.1 then (2 + p.2.1) / 3 else p.2.1 / 3 := by
  have hx' : x.1 ∈ cantorSet := x.2
  have hx :
      x.1 ∈ (· / 3) '' cantorSet ∪ (fun y : ℝ => (2 + y) / 3) '' cantorSet := by
    rw [← cantorSet_eq_union_halves]
    exact hx'
  rcases hx with hxL | hxR
  · rcases hxL with ⟨y, hy, hyx⟩
    refine ⟨(false, ⟨y, hy⟩), ?_⟩
    simpa using hyx.symm
  · rcases hxR with ⟨y, hy, hyx⟩
    refine ⟨(true, ⟨y, hy⟩), ?_⟩
    simpa using hyx.symm

/-- One decode step from a Cantor point: choose branch bit and predecessor point. -/
noncomputable def cantorSet_stepData (x : {x : ℝ // x ∈ cantorSet}) :
    {p : Bool × {y : ℝ // y ∈ cantorSet} //
      x.1 = if p.1 then (2 + p.2.1) / 3 else p.2.1 / 3} :=
  ⟨Classical.choose (cantorSet_step_exists x), Classical.choose_spec (cantorSet_step_exists x)⟩

noncomputable def cantorSet_step (x : {x : ℝ // x ∈ cantorSet}) :
    Bool × {y : ℝ // y ∈ cantorSet} :=
  (cantorSet_stepData x).1

theorem cantorSet_step_spec (x : {x : ℝ // x ∈ cantorSet}) :
    x.1 = if (cantorSet_step x).1 then (2 + (cantorSet_step x).2.1) / 3
      else (cantorSet_step x).2.1 / 3 :=
  (cantorSet_stepData x).2

/-- Recursive decoded tails from a Cantor point. -/
noncomputable def cantorSet_decodeTail :
    {x : ℝ // x ∈ cantorSet} → ℕ → {x : ℝ // x ∈ cantorSet}
  | x, 0 => x
  | x, n + 1 => (cantorSet_step (cantorSet_decodeTail x n)).2

/-- Decoded bitstream of a Cantor point. -/
noncomputable def cantorSet_decodeBits (x : {x : ℝ // x ∈ cantorSet}) (n : ℕ) : Bool :=
  (cantorSet_step (cantorSet_decodeTail x n)).1

/-- Numeric tail operator on bitstreams. -/
noncomputable def natTail (f : EvalPath) (n : ℕ) : EvalPath := fun k => f (n + k)

@[simp] theorem natTail_zero (f : EvalPath) : natTail f 0 = f := by
  funext k
  simp [natTail]

theorem cantorSet_decodeTail_step (x : {x : ℝ // x ∈ cantorSet}) (n : ℕ) :
    (cantorSet_decodeTail x n).1 =
      if cantorSet_decodeBits x n then (2 + (cantorSet_decodeTail x (n + 1)).1) / 3
      else (cantorSet_decodeTail x (n + 1)).1 / 3 := by
  simpa [cantorSet_decodeBits, cantorSet_decodeTail] using
    cantorSet_step_spec (cantorSet_decodeTail x n)

theorem cantorEncode_natTail_step (f : EvalPath) (n : ℕ) :
    HeytingLean.MirandaDynamics.Billiards.cantorEncode (natTail f n) =
      (if f n then (2 + HeytingLean.MirandaDynamics.Billiards.cantorEncode (natTail f (n + 1))) / 3
       else HeytingLean.MirandaDynamics.Billiards.cantorEncode (natTail f (n + 1)) / 3) := by
  have htail : (fun n_1 : ℕ => f (n + (n_1 + 1))) = natTail f (n + 1) := by
    funext k
    simp [natTail, Nat.add_left_comm, Nat.add_comm]
  simpa [natTail, Nat.add_left_comm, Nat.add_comm, htail] using
    (HeytingLean.MirandaDynamics.Billiards.cantorEncode_succ (fun k : ℕ => f (k + n)))

private theorem abs_sub_contract (b : Bool) (x x' y y' : ℝ)
    (hx : x = if b then (2 + x') / 3 else x' / 3)
    (hy : y = if b then (2 + y') / 3 else y' / 3) :
    |x - y| = |x' - y'| / 3 := by
  cases b
  · have hdiff : x' / 3 - y' / 3 = (x' - y') / 3 := by ring
    simp [hx, hy, hdiff, abs_div]
  · have hdiff : (2 + x') / 3 - (2 + y') / 3 = (x' - y') / 3 := by ring
    simp [hx, hy, hdiff, abs_div]

/-- The decode bitstream re-encodes to the original Cantor point. -/
theorem cantorSet_decodeBits_correct (x : {x : ℝ // x ∈ cantorSet}) :
    HeytingLean.MirandaDynamics.Billiards.cantorEncode (cantorSet_decodeBits x) = x.1 := by
  let f : EvalPath := cantorSet_decodeBits x
  let xTail : ℕ → ℝ := fun n => (cantorSet_decodeTail x n).1
  let yTail : ℕ → ℝ := fun n => HeytingLean.MirandaDynamics.Billiards.cantorEncode (natTail f n)
  let d : ℕ → ℝ := fun n => |xTail n - yTail n|
  have hstepX :
      ∀ n, xTail n =
        if f n then (2 + xTail (n + 1)) / 3 else xTail (n + 1) / 3 := by
    intro n
    simpa [xTail, f] using cantorSet_decodeTail_step x n
  have hstepY :
      ∀ n, yTail n =
        if f n then (2 + yTail (n + 1)) / 3 else yTail (n + 1) / 3 := by
    intro n
    simpa [yTail, f] using cantorEncode_natTail_step f n
  have hrec : ∀ n, d n = d (n + 1) / 3 := by
    intro n
    simpa [d, xTail, yTail] using
      abs_sub_contract (f n) (xTail n) (xTail (n + 1)) (yTail n) (yTail (n + 1))
        (hstepX n) (hstepY n)
  have hd_nonneg : ∀ n, 0 ≤ d n := by
    intro n
    exact abs_nonneg _
  have hd_le_one : ∀ n, d n ≤ 1 := by
    intro n
    have hxIcc : xTail n ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [xTail] using cantorSet_subset_unitInterval (cantorSet_decodeTail x n).2
    have hyIcc : yTail n ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [yTail] using
        (HeytingLean.MirandaDynamics.Billiards.cantorEncode_mem_Icc (natTail f n))
    have hlow : -1 ≤ xTail n - yTail n := by nlinarith [hxIcc.1, hxIcc.2, hyIcc.1, hyIcc.2]
    have hupp : xTail n - yTail n ≤ 1 := by nlinarith [hxIcc.1, hxIcc.2, hyIcc.1, hyIcc.2]
    have habs : |xTail n - yTail n| ≤ 1 := (abs_le).2 ⟨hlow, hupp⟩
    simpa [d] using habs
  have hd_pow : ∀ n : ℕ, d 0 = d n * ((1 / 3 : ℝ) ^ n) := by
    intro n
    induction n with
    | zero =>
      simp [d]
    | succ n ih =>
      calc
        d 0 = d n * ((1 / 3 : ℝ) ^ n) := ih
        _ = (d (n + 1) / 3) * ((1 / 3 : ℝ) ^ n) := by simp [hrec n]
        _ = d (n + 1) * ((1 / 3 : ℝ) ^ (n + 1)) := by
          ring_nf
  have hbound : ∀ n : ℕ, d 0 ≤ (1 / 3 : ℝ) ^ n := by
    intro n
    calc
      d 0 = d n * ((1 / 3 : ℝ) ^ n) := hd_pow n
      _ ≤ 1 * ((1 / 3 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_right (hd_le_one n) (pow_nonneg (by norm_num) n)
      _ = (1 / 3 : ℝ) ^ n := by ring
  have hd0_zero : d 0 = 0 := by
    by_contra hd0
    have hd0_pos : 0 < d 0 := lt_of_le_of_ne (hd_nonneg 0) (Ne.symm hd0)
    obtain ⟨n, hnlt⟩ :
        ∃ n : ℕ, (1 / 3 : ℝ) ^ n < d 0 :=
      exists_pow_lt_of_lt_one hd0_pos (by norm_num : (1 / 3 : ℝ) < 1)
    exact (not_lt_of_ge (hbound n)) hnlt
  have hxy : xTail 0 = yTail 0 := by
    have hsub : xTail 0 - yTail 0 = 0 := by
      simpa [d] using hd0_zero
    linarith
  simpa [xTail, yTail, f, natTail, cantorSet_decodeTail] using hxy.symm

/-- Surjectivity of the concrete typed Cantor encoding onto the typed Cantor set. -/
theorem evalPath_to_ternaryCantorSubtype_surjective :
    Function.Surjective evalPath_to_ternaryCantorSubtype := by
  intro x
  refine ⟨cantorSet_decodeBits x, ?_⟩
  apply Subtype.ext
  simpa [evalPath_to_ternaryCantorSubtype, evalPath_to_ternaryCantor] using
    cantorSet_decodeBits_correct x

/-- Unbundled surjectivity statement on `cantorSet`. -/
theorem evalPath_to_ternaryCantor_surjective_on_cantorSet :
    ∀ x ∈ cantorSet, ∃ p : EvalPath, evalPath_to_ternaryCantor p = x := by
  intro x hx
  rcases evalPath_to_ternaryCantorSubtype_surjective ⟨x, hx⟩ with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  exact congrArg Subtype.val hp

/-- Full topological bridge: concrete encoding gives a homeomorphism onto typed `cantorSet`. -/
noncomputable def evalPath_to_ternaryCantor_homeomorph_cantorSubtype :
    EvalPath ≃ₜ {x : ℝ // x ∈ cantorSet} :=
  ((continuous_evalPath_to_ternaryCantorSubtype.isClosedEmbedding
      evalPath_to_ternaryCantorSubtype_injective).isEmbedding).toHomeomorphOfSurjective
    evalPath_to_ternaryCantorSubtype_surjective

/-- Cardinality of the typed ternary Cantor set lane matches continuum. -/
theorem cantorSet_subtype_card_eq_continuum :
    #({x : ℝ // x ∈ cantorSet}) = Cardinal.continuum := by
  have hlower : Cardinal.continuum ≤ #({x : ℝ // x ∈ cantorSet}) := by
    have hmk : #EvalPath ≤ #({x : ℝ // x ∈ cantorSet}) :=
      Cardinal.mk_le_of_injective evalPath_to_ternaryCantorSubtype_injective
    simpa [evalPath_card] using hmk
  have hupper : #({x : ℝ // x ∈ cantorSet}) ≤ Cardinal.continuum := by
    have hsub : #({x : ℝ // x ∈ cantorSet}) ≤ #ℝ :=
      Cardinal.mk_subtype_le (fun x : ℝ => x ∈ cantorSet)
    simpa [Cardinal.mk_real] using hsub
  exact le_antisymm hupper hlower

/-- Full cardinal equivalence between path space and typed ternary Cantor set. -/
theorem evalPath_card_eq_ternaryCantorSubtype :
    #EvalPath = #({x : ℝ // x ∈ cantorSet}) := by
  calc
    #EvalPath = Cardinal.continuum := evalPath_card
    _ = #({x : ℝ // x ∈ cantorSet}) := cantorSet_subtype_card_eq_continuum.symm

/-- Full-set equivalence upgrade: EvalPath is equipotent to the typed ternary Cantor set. -/
noncomputable def evalPath_equiv_ternaryCantorSubtype :
    EvalPath ≃ {x : ℝ // x ∈ cantorSet} :=
  Classical.choice (Cardinal.eq.mp evalPath_card_eq_ternaryCantorSubtype)

/-- Glossary-level alias: CantorCutPath inherits the full typed Cantor-set equivalence. -/
noncomputable def cantorCut_equiv_ternaryCantorSubtype :
    CantorCutPath ≃ {x : ℝ // x ∈ cantorSet} :=
  evalPath_equiv_ternaryCantorSubtype

/-- The ternary Cantor set is uncountable (derived from the cardinal bridge). -/
theorem cantorSet_not_countable : ¬ (cantorSet : Set ℝ).Countable := by
  intro hcount
  have hle : #(cantorSet : Set ℝ) ≤ Cardinal.aleph0 :=
    (Cardinal.le_aleph0_iff_set_countable).2 hcount
  have hlt : Cardinal.aleph0 < #(cantorSet : Set ℝ) := by
    simpa [Cardinal.mk_set, cantorSet_subtype_card_eq_continuum] using
      (Cardinal.aleph0_lt_continuum)
  exact (not_lt_of_ge hle) hlt

/-- Topological-strengthening witness:
continuous injective Cantor-space map into the ternary Cantor set. -/
theorem exists_continuous_injective_evalPath_to_cantorSet :
    ∃ f : (ℕ → Bool) → ℝ, Set.range f ⊆ cantorSet ∧ Continuous f ∧ Function.Injective f :=
  IsClosed.exists_nat_bool_injection_of_not_countable (C := cantorSet)
    isClosed_cantorSet cantorSet_not_countable

/-- Subtype version of the continuous-injective Cantor-space embedding. -/
theorem exists_continuous_injective_evalPath_to_cantorSubtype :
    ∃ g : (ℕ → Bool) → {x : ℝ // x ∈ cantorSet}, Continuous g ∧ Function.Injective g := by
  rcases exists_continuous_injective_evalPath_to_cantorSet with ⟨f, hsub, hcont, hinj⟩
  refine ⟨fun p => ⟨f p, hsub ⟨p, rfl⟩⟩, ?_, ?_⟩
  · exact hcont.subtype_mk (fun p => hsub ⟨p, rfl⟩)
  · intro p q h
    apply hinj
    exact congrArg Subtype.val h

/-- Bundled embedding form for ATP/transport consumers. -/
theorem exists_continuous_evalPath_embedding_into_cantorSubtype :
    ∃ e : (ℕ → Bool) ↪ {x : ℝ // x ∈ cantorSet},
      Continuous (e : (ℕ → Bool) → {x : ℝ // x ∈ cantorSet}) := by
  rcases exists_continuous_injective_evalPath_to_cantorSubtype with ⟨g, hgcont, hginj⟩
  exact ⟨⟨g, hginj⟩, hgcont⟩

end HeytingLean.Genesis
