import Mathlib.Order.Heyting.Basic
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Double‑Negation Booleanization (skeleton)

Defines `RegDN Ω` as the fixed points of the double‑negation operator
`dn a := (a ⇨ ⊥) ⇨ ⊥` on a Heyting algebra. Provides the canonical
projection `toBoolDN : Ω → RegDN Ω` and basic lemmas showing idempotence
of `dn`. (Full `BooleanAlgebra` instance on `RegDN Ω` is left to a
separate, heavier pass.)
-/

namespace HeytingLean
namespace Logic

universe u

variable {Ω : Type u} [HeytingAlgebra Ω]

@[simp] def hnot (a : Ω) : Ω := a ⇨ ⊥
@[simp] def dn (a : Ω) : Ω := hnot (hnot a)

/-! Basic Heyting facts used to reason about `dn`. -/

lemma inf_himp_le (a b : Ω) : a ⊓ (a ⇨ b) ≤ b := by
  -- From `le_rfl : (a ⇨ b) ≤ (a ⇨ b)` and the adjunction
  have : (a ⇨ b) ⊓ a ≤ b := (le_himp_iff).mp (le_rfl : (a ⇨ b) ≤ a ⇨ b)
  simpa [inf_comm] using this

/-- Every element lies below its double-negation closure. -/
lemma le_dn (a : Ω) : a ≤ dn a := by
  -- `a ⊓ (a ⇨ ⊥) ≤ ⊥` implies `a ≤ (a ⇨ ⊥) ⇨ ⊥`
  have : a ⊓ hnot a ≤ (⊥ : Ω) := by simpa [hnot] using (inf_himp_le a (⊥ : Ω))
  exact (le_himp_iff).mpr this

/-- Implication is antitone in its left argument. -/
lemma himp_antitone_left {a b c : Ω} (h : a ≤ b) : b ⇨ c ≤ a ⇨ c := by
  -- Show `(b ⇨ c) ⊓ a ≤ c` then use `le_himp_iff`.
  have h1 : (b ⇨ c) ⊓ a ≤ (b ⇨ c) := inf_le_left
  have h2 : (b ⇨ c) ⊓ a ≤ b := le_trans inf_le_right h
  have hmono : (b ⇨ c) ⊓ a ≤ (b ⇨ c) ⊓ b := le_inf h1 h2
  have hc : (b ⇨ c) ⊓ b ≤ c := by simpa [inf_comm] using (inf_himp_le b c)
  have hca : (b ⇨ c) ⊓ a ≤ c := le_trans hmono hc
  exact (le_himp_iff).mpr hca

/-- Double negation is idempotent on any Heyting algebra. -/
lemma dn_idem (a : Ω) : dn (dn a) = dn a := by
  -- Show both inequalities and use antisymmetry.
  apply le_antisymm
  · -- `dn (dn a) ≤ dn a` via antitone of `hnot` and `le_dn (hnot a)`.
    -- From `hnot a ≤ dn (hnot a)` and antitone of `hnot`.
    have hx : hnot a ≤ dn (hnot a) := le_dn (hnot a)
    have : hnot (dn (hnot a)) ≤ hnot (hnot a) := himp_antitone_left (a := hnot a) (b := dn (hnot a)) (c := ⊥) hx
    simpa [dn, hnot] using this
  · -- `dn a ≤ dn (dn a)` via `a ≤ dn a` and antitone of `hnot` twice.
    have hx : a ≤ dn a := le_dn a
    -- From `a ≤ dn a` we get `hnot (dn a) ≤ hnot a` (antitone in left).
    have hneg : hnot (dn a) ≤ hnot a := himp_antitone_left (a := a) (b := dn a) (c := ⊥) hx
    -- Apply antitone again (flip inequality): `dn a = hnot (hnot a) ≤ hnot (hnot (dn a)) = dn (dn a)`.
    have := himp_antitone_left (a := hnot (dn a)) (b := hnot a) (c := ⊥) hneg
    simpa [dn, hnot] using this

/-- Subtype of elements fixed by double negation (`dn a = a`). -/
def RegDN (Ω : Type u) [HeytingAlgebra Ω] := {a : Ω // dn a = a}

namespace RegDN

instance instInhabited : Inhabited (RegDN Ω) :=
  -- dn ⊥ = ⊥ in any Heyting algebra
  ⟨⟨(⊥ : Ω), by
      -- `dn ⊥ = (⊥ ⇨ ⊥) ⇨ ⊥ = ⊤ ⇨ ⊥ = ⊥`
      simp [dn, hnot]⟩⟩

-- DecidableEq for this subtype is not required here; provide on demand.

@[simp] def val (x : RegDN Ω) : Ω := x.1
instance : Coe (RegDN Ω) Ω where
  coe := val

/-- Project an arbitrary `Ω`-element to its double-negation fixed point. -/
@[simp] def toBoolDN (a : Ω) : RegDN Ω := ⟨dn a, dn_idem a⟩

@[simp] theorem toBoolDN_val (a : Ω) : (toBoolDN (Ω := Ω) a).1 = dn a := rfl

@[simp] theorem toBoolDN_id (x : RegDN Ω) : toBoolDN (Ω := Ω) x.1 = x := by
  cases x with
  | mk a ha =>
    -- Coerce equality of subtypes via proof irrelevance
    apply Subtype.ext
    -- underlying values equal by the fixed-point witness
    simpa [toBoolDN] using ha

end RegDN

/-! ## Operations lifted via double‑negation closure

Define Boolean‑style operations by computing on the carrier and closing with `dn`.
These are library-only helpers; we do not install a full instance here.
-/

namespace RegDN

@[simp] def top : RegDN Ω := ⟨dn (⊤ : Ω), by simp [dn, hnot]⟩
@[simp] def bot : RegDN Ω := ⟨dn (⊥ : Ω), by simp [dn, hnot]⟩

@[simp] def inf (x y : RegDN Ω) : RegDN Ω :=
  ⟨dn (x.1 ⊓ y.1), dn_idem (x.1 ⊓ y.1)⟩

@[simp] def sup (x y : RegDN Ω) : RegDN Ω :=
  ⟨dn (x.1 ⊔ y.1), dn_idem (x.1 ⊔ y.1)⟩

@[simp] def compl (x : RegDN Ω) : RegDN Ω :=
  ⟨dn (hnot x.1), dn_idem (hnot x.1)⟩

/-- Extracting values of the lifted Boolean `top` and `bot`. -/
@[simp] lemma top_val : (top (Ω := Ω)).1 = (⊤ : Ω) := by simp [top, dn, hnot]
@[simp] lemma bot_val : (bot (Ω := Ω)).1 = (⊥ : Ω) := by simp [bot, dn, hnot]

/-- Infimum in `RegDN` is the double-negation closure of the underlying meet. -/
@[simp] lemma inf_commDN (x y : RegDN Ω) : inf x y = inf y x := by
  apply Subtype.ext
  change dn (x.1 ⊓ y.1) = dn (y.1 ⊓ x.1)
  have h : x.1 ⊓ y.1 = y.1 ⊓ x.1 := by
    simpa using (_root_.inf_comm (x.1) (y.1))
  simpa using congrArg dn h

@[simp] lemma sup_commDN (x y : RegDN Ω) : sup x y = sup y x := by
  apply Subtype.ext
  change dn (x.1 ⊔ y.1) = dn (y.1 ⊔ x.1)
  have h : x.1 ⊔ y.1 = y.1 ⊔ x.1 := by
    simpa using (_root_.sup_comm (x.1) (y.1))
  simpa using congrArg dn h

end RegDN

/-! ## Boolean algebra instance under `[BooleanAlgebra Ω]`

When the carrier `Ω` is already a Boolean algebra, double negation is the identity,
so `RegDN Ω` is isomorphic to `Ω`. We transport the full lattice/Boolean structure.
-/

section BooleanTransport

variable {ΩB : Type u} [BooleanAlgebra ΩB]

@[simp] lemma dn_eq_self (a : ΩB) : dn a = a := by
  -- In a Boolean algebra, `a ⇨ ⊥ = aᶜ`, hence `dn a = (aᶜ)ᶜ = a`.
  simp [dn, hnot, himp_eq, compl_compl]

instance : Max (RegDN ΩB) :=
  ⟨fun x y => ⟨x.1 ⊔ y.1, by simp [dn_eq_self]⟩⟩

instance : Min (RegDN ΩB) :=
  ⟨fun x y => ⟨x.1 ⊓ y.1, by simp [dn_eq_self]⟩⟩

@[simp] lemma coe_sup_max (x y : RegDN ΩB) : ((x ⊔ y : RegDN ΩB) : ΩB) = x.1 ⊔ y.1 := rfl
@[simp] lemma coe_inf_min (x y : RegDN ΩB) : ((x ⊓ y : RegDN ΩB) : ΩB) = x.1 ⊓ y.1 := rfl

instance : Top (RegDN ΩB) := ⟨⟨⊤, by simp [dn_eq_self]⟩⟩
instance : Bot (RegDN ΩB) := ⟨⟨⊥, by simp [dn_eq_self]⟩⟩

@[simp] lemma coe_top' : ((⊤ : RegDN ΩB) : ΩB) = (⊤ : ΩB) := rfl
@[simp] lemma coe_bot' : ((⊥ : RegDN ΩB) : ΩB) = (⊥ : ΩB) := rfl

instance : HasCompl (RegDN ΩB) where
  compl x := ⟨hnot x.1, by simp [dn, hnot, dn_eq_self]⟩

instance : SDiff (RegDN ΩB) where
  sdiff x y := RegDN.inf x (HasCompl.compl y)

instance : HImp (RegDN ΩB) where
  himp x y := RegDN.sup y (HasCompl.compl x)

private lemma coe_compl (x : RegDN ΩB) : (HasCompl.compl x : RegDN ΩB).1 = x.1ᶜ := by
  simp [HasCompl.compl, hnot, dn_eq_self]

noncomputable instance : BooleanAlgebra (RegDN ΩB) :=
  Function.Injective.booleanAlgebra
    (f := (fun x : RegDN ΩB => (x : ΩB)))
    (hf := Subtype.coe_injective)
    (map_sup := by intro x y; rfl)
    (map_inf := by intro x y; rfl)
    (map_top := rfl)
    (map_bot := rfl)
    (map_compl := by intro x; simp [HasCompl.compl, hnot, dn_eq_self])
    (map_sdiff := by intro x y; simp [SDiff.sdiff, RegDN.inf, HasCompl.compl, hnot, dn_eq_self, sdiff_eq])
    (map_himp := by intro x y; simp [HImp.himp, RegDN.sup, HasCompl.compl, hnot, dn_eq_self, himp_eq])

end BooleanTransport

end Logic
end HeytingLean
