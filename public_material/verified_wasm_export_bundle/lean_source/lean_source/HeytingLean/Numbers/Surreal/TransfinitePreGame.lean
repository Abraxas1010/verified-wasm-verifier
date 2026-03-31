import HeytingLean.Numbers.Ordinal.Notation
import HeytingLean.Numbers.SurrealCore

/-!
# Transfinite birthday toy model (Surreal)

This module provides a **small, executable** extension of the existing finite surreal
pipeline that can *represent and compute* **transfinite ordinal birthdays** for a
restricted (but meaningful) class of pre-games.

Design goal:
- Keep the representation strictly-positive (Lean inductive types).
- Allow a few common infinite option sets in finite syntax (e.g. `{0,1,2,...}`),
  so that canonical examples like the surreal `ω = {0,1,2,... | }` obtain birthday `ω`.

Non-goals:
- Full Conway theory (quotienting, full addition/multiplication, etc.).
- Arbitrary (non-compactly-presented) infinite option sets.

Ordinal layer:
- Uses `HeytingLean.Numbers.Ordinal.OrdinalCNF` (Mathlib's `NONote`, below `ε₀`).
- All comparisons/arithmetic here are computable.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.Ordinal

namespace TransfinitePreGame

/-! ## Compact option sets -/

mutual

  /-- A compact presentation of (possibly infinite) option sets. -/
  inductive OptionSet : Type
    | finite (xs : List PreGame)
    /-- The infinite family `{0, 1, 2, ...}` of finite naturals (as pre-games). -/
    | nats
    /-- The infinite family `{ω, ω+1, ω+2, ...}`. -/
    | omegaPlusNats
    /-- The infinite family `{ω+ω, ω+ω+1, ω+ω+2, ...}`. -/
    | omegaTimesTwoPlusNats
    /-- Union of option sets (compact syntax). -/
    | union (a b : OptionSet)
    deriving Repr

  /-- A pre-game built from compact option sets. -/
  inductive PreGame : Type
    | cut (L R : OptionSet)
    deriving Repr

end

namespace PreGame

def zero : PreGame :=
  .cut (.finite []) (.finite [])

def nat : Nat → PreGame
  | 0 => zero
  | Nat.succ n => .cut (.finite [nat n]) (.finite [])

def omega : PreGame :=
  .cut .nats (.finite [])

/-- `ω + ω` as a compact game: `{ω, ω+1, ω+2, ... | }`. -/
def omegaTimesTwo : PreGame :=
  .cut .omegaPlusNats (.finite [])

mutual
  /-- `ω + n` presented as `{ 0,1,2,..., ω, ω+1, ..., ω+(n-1) | }`. -/
  def omegaPlusNat : Nat → PreGame
    | 0 => omega
    | Nat.succ n =>
        .cut (.union .nats (.finite (omegaPlusNatList (Nat.succ n)))) (.finite [])

  /-- The finite prefix `[ω+0, ω+1, ..., ω+(n-1)]` (in reverse order). -/
  def omegaPlusNatList : Nat → List PreGame
    | 0 => []
    | Nat.succ n => omegaPlusNat n :: omegaPlusNatList n

  /-- `ω+ω+n` presented as `{0,1,2,..., ω,ω+1,..., ω+ω,ω+ω+1,...,ω+ω+(n-1) | }`. -/
  def omegaTimesTwoPlusNat : Nat → PreGame
    | 0 => omegaTimesTwo
    | Nat.succ n =>
        .cut
          (.union .nats (.union .omegaPlusNats (.finite (omegaTimesTwoPlusNatList (Nat.succ n)))))
          (.finite [])

  /-- The finite prefix `[ω+ω+0, ω+ω+1, ..., ω+ω+(n-1)]` (in reverse order). -/
  def omegaTimesTwoPlusNatList : Nat → List PreGame
    | 0 => []
    | Nat.succ n => omegaTimesTwoPlusNat n :: omegaTimesTwoPlusNatList n
end

/-- `ω + ω + ω` as a compact game: `{ω+ω, ω+ω+1, ω+ω+2, ... | }`. -/
def omegaTimesThree : PreGame :=
  .cut .omegaTimesTwoPlusNats (.finite [])

end PreGame

/-! ## Birthdays -/

mutual
  /-- Supremum of successor-birthdays over an option set:
  `sup { birth(x) + 1 | x ∈ options }`. -/
  def supSucc (opts : OptionSet) : OrdinalCNF :=
    match opts with
    | .finite xs =>
        OrdinalCNF.supList (xs.map (fun g => OrdinalCNF.succ (birth g)))
    | .nats =>
        -- `sup { n+1 | n ∈ ℕ } = ω`
        OrdinalCNF.omega
    | .omegaPlusNats =>
        -- `sup { (ω+n)+1 | n ∈ ℕ } = ω+ω`
        OrdinalCNF.omega + OrdinalCNF.omega
    | .omegaTimesTwoPlusNats =>
        -- `sup { (ω+ω+n)+1 | n ∈ ℕ } = ω+ω+ω`
        OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.omega
    | .union a b =>
        OrdinalCNF.max (supSucc a) (supSucc b)

  /-- Constructive ordinal birthday of a pre-game. -/
  def birth : PreGame → OrdinalCNF
    | .cut L R => OrdinalCNF.max (supSucc L) (supSucc R)
end

@[simp] theorem birth_nat_zero :
    birth (PreGame.nat 0) = (0 : OrdinalCNF) := by
  simp [PreGame.nat, PreGame.zero, birth, supSucc]

@[simp] theorem birth_nat_succ (n : Nat) :
    birth (PreGame.nat (Nat.succ n)) =
      OrdinalCNF.succ (birth (PreGame.nat n)) := by
  simp [PreGame.nat, birth, supSucc, OrdinalCNF.succ]

@[simp] theorem birth_omega :
    birth PreGame.omega = OrdinalCNF.omega := by
  simp [PreGame.omega, birth, supSucc]

@[simp] theorem birth_omegaTimesTwo :
    birth PreGame.omegaTimesTwo = OrdinalCNF.omega + OrdinalCNF.omega := by
  simp [PreGame.omegaTimesTwo, birth, supSucc, OrdinalCNF.max_zero_right]

@[simp] theorem birth_omegaTimesThree :
    birth PreGame.omegaTimesThree = OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.omega := by
  simp [PreGame.omegaTimesThree, birth, supSucc, OrdinalCNF.max_zero_right]

@[simp] theorem birth_omegaPlusNat_zero :
    birth (PreGame.omegaPlusNat 0) = OrdinalCNF.omega := by
  simp [PreGame.omegaPlusNat, birth_omega]

@[simp] theorem birth_omegaTimesTwoPlusNat_zero :
    birth (PreGame.omegaTimesTwoPlusNat 0) = OrdinalCNF.omega + OrdinalCNF.omega := by
  simp [PreGame.omegaTimesTwoPlusNat, birth_omegaTimesTwo]

/-- Native birthday recurrence decomposition for `ω+n` constructors. -/
theorem birth_omegaPlusNat_succ_unfold (n : Nat) :
    birth (PreGame.omegaPlusNat (Nat.succ n)) =
      OrdinalCNF.max OrdinalCNF.omega
        (OrdinalCNF.supList
          ((PreGame.omegaPlusNatList (Nat.succ n)).map
            (fun g => OrdinalCNF.succ (birth g)))) := by
  simp [PreGame.omegaPlusNat, birth, supSucc, OrdinalCNF.max_zero_right]

/-- Native birthday recurrence decomposition for `ω+ω+n` constructors. -/
theorem birth_omegaTimesTwoPlusNat_succ_unfold (n : Nat) :
    birth (PreGame.omegaTimesTwoPlusNat (Nat.succ n)) =
      OrdinalCNF.max OrdinalCNF.omega
        (OrdinalCNF.max (OrdinalCNF.omega + OrdinalCNF.omega)
          (OrdinalCNF.supList
            ((PreGame.omegaTimesTwoPlusNatList (Nat.succ n)).map
              (fun g => OrdinalCNF.succ (birth g))))) := by
  simp [PreGame.omegaTimesTwoPlusNat, birth, supSucc, OrdinalCNF.max_zero_right]

theorem birth_omegaPlusNat_ge_omega (n : Nat) :
    OrdinalCNF.omega ≤ birth (PreGame.omegaPlusNat n) := by
  cases n with
  | zero =>
      simp [birth_omegaPlusNat_zero]
  | succ n =>
      rw [birth_omegaPlusNat_succ_unfold]
      exact OrdinalCNF.le_max_left _ _

theorem birth_omegaTimesTwoPlusNat_ge_omegaTimesTwo (n : Nat) :
    OrdinalCNF.omega + OrdinalCNF.omega ≤ birth (PreGame.omegaTimesTwoPlusNat n) := by
  cases n with
  | zero =>
      simp [birth_omegaTimesTwoPlusNat_zero]
  | succ n =>
      rw [birth_omegaTimesTwoPlusNat_succ_unfold]
      have hInner :
          OrdinalCNF.omega + OrdinalCNF.omega ≤
            OrdinalCNF.max (OrdinalCNF.omega + OrdinalCNF.omega)
              (OrdinalCNF.supList
                ((PreGame.omegaTimesTwoPlusNatList (Nat.succ n)).map
                  (fun g => OrdinalCNF.succ (birth g)))) :=
        OrdinalCNF.le_max_left _ _
      have hOuter :
          OrdinalCNF.max (OrdinalCNF.omega + OrdinalCNF.omega)
            (OrdinalCNF.supList
              ((PreGame.omegaTimesTwoPlusNatList (Nat.succ n)).map
                (fun g => OrdinalCNF.succ (birth g)))) ≤
            OrdinalCNF.max OrdinalCNF.omega
              (OrdinalCNF.max (OrdinalCNF.omega + OrdinalCNF.omega)
                (OrdinalCNF.supList
                  ((PreGame.omegaTimesTwoPlusNatList (Nat.succ n)).map
                    (fun g => OrdinalCNF.succ (birth g))))) :=
        OrdinalCNF.le_max_right _ _
      exact le_trans hInner hOuter

theorem mem_omegaPlusNatList_exists :
    ∀ {m : Nat} {g : PreGame}, g ∈ PreGame.omegaPlusNatList m →
      ∃ k : Nat, k < m ∧ g = PreGame.omegaPlusNat k
  | 0, _, hg => by
      simp [PreGame.omegaPlusNatList] at hg
  | Nat.succ m, g, hg => by
      simp [PreGame.omegaPlusNatList] at hg
      rcases hg with rfl | hg
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · rcases mem_omegaPlusNatList_exists hg with ⟨k, hk, rfl⟩
        exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m), rfl⟩

theorem mem_omegaTimesTwoPlusNatList_exists :
    ∀ {m : Nat} {g : PreGame}, g ∈ PreGame.omegaTimesTwoPlusNatList m →
      ∃ k : Nat, k < m ∧ g = PreGame.omegaTimesTwoPlusNat k
  | 0, _, hg => by
      simp [PreGame.omegaTimesTwoPlusNatList] at hg
  | Nat.succ m, g, hg => by
      simp [PreGame.omegaTimesTwoPlusNatList] at hg
      rcases hg with rfl | hg
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · rcases mem_omegaTimesTwoPlusNatList_exists hg with ⟨k, hk, rfl⟩
        exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m), rfl⟩

/-- Native closed form for compact `ω+n` constructors. -/
theorem birth_omegaPlusNat_eq_omega_add_ofNat (n : Nat) :
    birth (PreGame.omegaPlusNat n) = OrdinalCNF.omega + OrdinalCNF.ofNat n := by
  refine Nat.strongRecOn n ?_
  intro n ih
  cases n with
  | zero =>
      native_decide
  | succ n =>
      rw [birth_omegaPlusNat_succ_unfold]
      let ys :=
        (PreGame.omegaPlusNatList (Nat.succ n)).map
          (fun g => OrdinalCNF.succ (birth g))
      have hHeadMem : OrdinalCNF.succ (birth (PreGame.omegaPlusNat n)) ∈ ys := by
        dsimp [ys]
        simp [PreGame.omegaPlusNatList]
      have hLowerHead :
          OrdinalCNF.succ (birth (PreGame.omegaPlusNat n)) ≤ OrdinalCNF.supList ys :=
        OrdinalCNF.le_supList_of_mem hHeadMem
      have hLower :
          OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) ≤
            OrdinalCNF.max OrdinalCNF.omega (OrdinalCNF.supList ys) := by
        have hEqPrev :
            birth (PreGame.omegaPlusNat n) = OrdinalCNF.omega + OrdinalCNF.ofNat n :=
          ih n (Nat.lt_succ_self n)
        have hSuccPrev :
            OrdinalCNF.succ (birth (PreGame.omegaPlusNat n)) =
              OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
          calc
            OrdinalCNF.succ (birth (PreGame.omegaPlusNat n))
                = (birth (PreGame.omegaPlusNat n)) + OrdinalCNF.ofNat 1 := by
                    simp [OrdinalCNF.succ, OrdinalCNF.ofNat]
            _ = (OrdinalCNF.omega + OrdinalCNF.ofNat n) + OrdinalCNF.ofNat 1 := by
                    rw [hEqPrev]
            _ = OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
                    calc
                      (OrdinalCNF.omega + OrdinalCNF.ofNat n) + OrdinalCNF.ofNat 1
                          = OrdinalCNF.omega + (OrdinalCNF.ofNat n + OrdinalCNF.ofNat 1) := by
                              rw [OrdinalCNF.add_assoc]
                      _ = OrdinalCNF.omega + OrdinalCNF.ofNat (n + 1) := by
                              rw [OrdinalCNF.ofNat_add_one]
                      _ = OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
                              simp [Nat.succ_eq_add_one]
        have hLower' :
            OrdinalCNF.succ (birth (PreGame.omegaPlusNat n)) ≤
              OrdinalCNF.max OrdinalCNF.omega (OrdinalCNF.supList ys) :=
          le_trans hLowerHead (OrdinalCNF.le_max_right _ _)
        simpa [hSuccPrev] using hLower'
      have hUpper :
          OrdinalCNF.max OrdinalCNF.omega (OrdinalCNF.supList ys) ≤
            OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
        apply OrdinalCNF.max_le
        · have hω : OrdinalCNF.omega ≤ birth (PreGame.omegaPlusNat n) :=
            birth_omegaPlusNat_ge_omega n
          have hs :
              birth (PreGame.omegaPlusNat n) ≤
                OrdinalCNF.succ (birth (PreGame.omegaPlusNat n)) := by
            simpa [OrdinalCNF.succ, OrdinalCNF.ofNat] using
              OrdinalCNF.le_add_right (birth (PreGame.omegaPlusNat n)) (OrdinalCNF.ofNat 1)
          have hωs : OrdinalCNF.omega ≤ OrdinalCNF.succ (birth (PreGame.omegaPlusNat n)) :=
            le_trans hω hs
          have hEqPrev :
              birth (PreGame.omegaPlusNat n) = OrdinalCNF.omega + OrdinalCNF.ofNat n :=
            ih n (Nat.lt_succ_self n)
          have hSuccPrev :
              OrdinalCNF.succ (birth (PreGame.omegaPlusNat n)) =
                OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
            calc
              OrdinalCNF.succ (birth (PreGame.omegaPlusNat n))
                  = (birth (PreGame.omegaPlusNat n)) + OrdinalCNF.ofNat 1 := by
                      simp [OrdinalCNF.succ, OrdinalCNF.ofNat]
              _ = (OrdinalCNF.omega + OrdinalCNF.ofNat n) + OrdinalCNF.ofNat 1 := by
                      rw [hEqPrev]
              _ = OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
                      calc
                        (OrdinalCNF.omega + OrdinalCNF.ofNat n) + OrdinalCNF.ofNat 1
                            = OrdinalCNF.omega + (OrdinalCNF.ofNat n + OrdinalCNF.ofNat 1) := by
                                rw [OrdinalCNF.add_assoc]
                        _ = OrdinalCNF.omega + OrdinalCNF.ofNat (n + 1) := by
                                rw [OrdinalCNF.ofNat_add_one]
                        _ = OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
                                simp [Nat.succ_eq_add_one]
          simpa [hSuccPrev] using hωs
        · apply OrdinalCNF.supList_le_of_forall
          intro x hx
          rcases List.mem_map.1 hx with ⟨g, hg, rfl⟩
          rcases mem_omegaPlusNatList_exists hg with ⟨k, hk, rfl⟩
          have hkLe : k ≤ n := Nat.lt_succ_iff.mp hk
          have hEqk :
              birth (PreGame.omegaPlusNat k) = OrdinalCNF.omega + OrdinalCNF.ofNat k :=
            ih k hk
          have hkNat : OrdinalCNF.ofNat k ≤ OrdinalCNF.ofNat n := by
            change NONote.repr (OrdinalCNF.ofNat k) ≤ NONote.repr (OrdinalCNF.ofNat n)
            simp [OrdinalCNF.ofNat, NONote.ofNat, NONote.repr]
            exact_mod_cast hkLe
          have hAdd :
              OrdinalCNF.omega + OrdinalCNF.ofNat k ≤
                OrdinalCNF.omega + OrdinalCNF.ofNat n :=
            OrdinalCNF.add_le_add_left (c := OrdinalCNF.omega) hkNat
          calc
            OrdinalCNF.succ (birth (PreGame.omegaPlusNat k))
                = (OrdinalCNF.omega + OrdinalCNF.ofNat k) + OrdinalCNF.ofNat 1 := by
                    simp [OrdinalCNF.succ, OrdinalCNF.ofNat, hEqk]
            _ ≤ (OrdinalCNF.omega + OrdinalCNF.ofNat n) + OrdinalCNF.ofNat 1 :=
                  OrdinalCNF.add_le_add_right hAdd
            _ = OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
                  calc
                    (OrdinalCNF.omega + OrdinalCNF.ofNat n) + OrdinalCNF.ofNat 1
                        = OrdinalCNF.omega + (OrdinalCNF.ofNat n + OrdinalCNF.ofNat 1) := by
                            rw [OrdinalCNF.add_assoc]
                    _ = OrdinalCNF.omega + OrdinalCNF.ofNat (n + 1) := by
                            rw [OrdinalCNF.ofNat_add_one]
                    _ = OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
                            simp [Nat.succ_eq_add_one]
      exact le_antisymm hUpper hLower

/-- Native closed form for compact `ω+ω+n` constructors. -/
theorem birth_omegaTimesTwoPlusNat_eq_omegaTimesTwo_add_ofNat (n : Nat) :
    birth (PreGame.omegaTimesTwoPlusNat n) =
      OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat n := by
  refine Nat.strongRecOn n ?_
  intro n ih
  cases n with
  | zero =>
      native_decide
  | succ n =>
      rw [birth_omegaTimesTwoPlusNat_succ_unfold]
      let ys :=
        (PreGame.omegaTimesTwoPlusNatList (Nat.succ n)).map
          (fun g => OrdinalCNF.succ (birth g))
      have hHeadMem : OrdinalCNF.succ (birth (PreGame.omegaTimesTwoPlusNat n)) ∈ ys := by
        dsimp [ys]
        simp [PreGame.omegaTimesTwoPlusNatList]
      have hLowerHead :
          OrdinalCNF.succ (birth (PreGame.omegaTimesTwoPlusNat n)) ≤ OrdinalCNF.supList ys :=
        OrdinalCNF.le_supList_of_mem hHeadMem
      have hLower :
          OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) ≤
            OrdinalCNF.max OrdinalCNF.omega
              (OrdinalCNF.max (OrdinalCNF.omega + OrdinalCNF.omega) (OrdinalCNF.supList ys)) := by
        have hEqPrev :
            birth (PreGame.omegaTimesTwoPlusNat n) =
              OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat n :=
          ih n (Nat.lt_succ_self n)
        have hSuccPrev :
            OrdinalCNF.succ (birth (PreGame.omegaTimesTwoPlusNat n)) =
              OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
          calc
            OrdinalCNF.succ (birth (PreGame.omegaTimesTwoPlusNat n))
                = (birth (PreGame.omegaTimesTwoPlusNat n)) + OrdinalCNF.ofNat 1 := by
                    simp [OrdinalCNF.succ, OrdinalCNF.ofNat]
            _ = (OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat n) + OrdinalCNF.ofNat 1 := by
                    rw [hEqPrev]
            _ = OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
                    calc
                      (OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat n) + OrdinalCNF.ofNat 1
                          = (OrdinalCNF.omega + OrdinalCNF.omega) +
                              (OrdinalCNF.ofNat n + OrdinalCNF.ofNat 1) := by
                              rw [OrdinalCNF.add_assoc]
                      _ = (OrdinalCNF.omega + OrdinalCNF.omega) + OrdinalCNF.ofNat (n + 1) := by
                              rw [OrdinalCNF.ofNat_add_one]
                      _ = OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
                              simp [Nat.succ_eq_add_one]
        have hLower' :
            OrdinalCNF.succ (birth (PreGame.omegaTimesTwoPlusNat n)) ≤
              OrdinalCNF.max OrdinalCNF.omega
                (OrdinalCNF.max (OrdinalCNF.omega + OrdinalCNF.omega) (OrdinalCNF.supList ys)) := by
          have h1 : OrdinalCNF.succ (birth (PreGame.omegaTimesTwoPlusNat n)) ≤
              OrdinalCNF.max (OrdinalCNF.omega + OrdinalCNF.omega) (OrdinalCNF.supList ys) :=
            le_trans hLowerHead (OrdinalCNF.le_max_right _ _)
          exact le_trans h1 (OrdinalCNF.le_max_right _ _)
        simpa [hSuccPrev] using hLower'
      have hUpper :
          OrdinalCNF.max OrdinalCNF.omega
            (OrdinalCNF.max (OrdinalCNF.omega + OrdinalCNF.omega) (OrdinalCNF.supList ys)) ≤
              OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
        apply OrdinalCNF.max_le
        · have hωω : OrdinalCNF.omega ≤ OrdinalCNF.omega + OrdinalCNF.omega := by
            simpa [OrdinalCNF.ofNat] using
              (OrdinalCNF.le_add_right OrdinalCNF.omega OrdinalCNF.omega)
          have hωωn :
              OrdinalCNF.omega + OrdinalCNF.omega ≤
                OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
            simpa [OrdinalCNF.add_assoc] using
              (OrdinalCNF.le_add_right
                (OrdinalCNF.omega + OrdinalCNF.omega)
                (OrdinalCNF.ofNat (Nat.succ n)))
          exact le_trans hωω hωωn
        · apply OrdinalCNF.max_le
          · simpa [OrdinalCNF.add_assoc] using
              (OrdinalCNF.le_add_right
                (OrdinalCNF.omega + OrdinalCNF.omega)
                (OrdinalCNF.ofNat (Nat.succ n)))
          · apply OrdinalCNF.supList_le_of_forall
            intro x hx
            rcases List.mem_map.1 hx with ⟨g, hg, rfl⟩
            rcases mem_omegaTimesTwoPlusNatList_exists hg with ⟨k, hk, rfl⟩
            have hkLe : k ≤ n := Nat.lt_succ_iff.mp hk
            have hEqk :
                birth (PreGame.omegaTimesTwoPlusNat k) =
                  OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat k :=
              ih k hk
            have hkNat : OrdinalCNF.ofNat k ≤ OrdinalCNF.ofNat n := by
              change NONote.repr (OrdinalCNF.ofNat k) ≤ NONote.repr (OrdinalCNF.ofNat n)
              simp [OrdinalCNF.ofNat, NONote.ofNat, NONote.repr]
              exact_mod_cast hkLe
            have hAdd :
                OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat k ≤
                  OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat n :=
              by
                have hCore :
                    OrdinalCNF.omega + OrdinalCNF.ofNat k ≤
                      OrdinalCNF.omega + OrdinalCNF.ofNat n :=
                  OrdinalCNF.add_le_add_left (c := OrdinalCNF.omega) hkNat
                have hCore' :
                    OrdinalCNF.omega + (OrdinalCNF.omega + OrdinalCNF.ofNat k) ≤
                      OrdinalCNF.omega + (OrdinalCNF.omega + OrdinalCNF.ofNat n) :=
                  OrdinalCNF.add_le_add_left (c := OrdinalCNF.omega) hCore
                calc
                  OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat k
                      = OrdinalCNF.omega + (OrdinalCNF.omega + OrdinalCNF.ofNat k) := by
                          rw [OrdinalCNF.add_assoc]
                  _ ≤ OrdinalCNF.omega + (OrdinalCNF.omega + OrdinalCNF.ofNat n) := hCore'
                  _ = OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat n := by
                          rw [OrdinalCNF.add_assoc]
            calc
              OrdinalCNF.succ (birth (PreGame.omegaTimesTwoPlusNat k))
                  = (OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat k) + OrdinalCNF.ofNat 1 := by
                      simp [OrdinalCNF.succ, OrdinalCNF.ofNat, hEqk]
              _ ≤ (OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat n) + OrdinalCNF.ofNat 1 :=
                    OrdinalCNF.add_le_add_right hAdd
              _ = OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
                    calc
                      (OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat n) + OrdinalCNF.ofNat 1
                          = (OrdinalCNF.omega + OrdinalCNF.omega) +
                              (OrdinalCNF.ofNat n + OrdinalCNF.ofNat 1) := by
                              rw [OrdinalCNF.add_assoc]
                      _ = (OrdinalCNF.omega + OrdinalCNF.omega) + OrdinalCNF.ofNat (n + 1) := by
                              rw [OrdinalCNF.ofNat_add_one]
                      _ = OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat (Nat.succ n) := by
                              simp [Nat.succ_eq_add_one]
      exact le_antisymm hUpper hLower

@[simp] theorem birth_omegaPlusNat_one :
    birth (PreGame.omegaPlusNat 1) = OrdinalCNF.omega + OrdinalCNF.ofNat 1 := by
  native_decide

@[simp] theorem birth_omegaPlusNat_two :
    birth (PreGame.omegaPlusNat 2) = OrdinalCNF.omega + OrdinalCNF.ofNat 2 := by
  native_decide

@[simp] theorem birth_omegaPlusNat_three :
    birth (PreGame.omegaPlusNat 3) = OrdinalCNF.omega + OrdinalCNF.ofNat 3 := by
  native_decide

@[simp] theorem birth_omegaTimesTwoPlusNat_one :
    birth (PreGame.omegaTimesTwoPlusNat 1) =
      OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat 1 := by
  native_decide

@[simp] theorem birth_omegaTimesTwoPlusNat_two :
    birth (PreGame.omegaTimesTwoPlusNat 2) =
      OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat 2 := by
  native_decide

@[simp] theorem birth_omegaTimesTwoPlusNat_three :
    birth (PreGame.omegaTimesTwoPlusNat 3) =
      OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat 3 := by
  native_decide

namespace OptionSet

/-- Bounded, executable enumeration of the first `k` options of a compact set.

This is intended for *runtime demos* and bounded checks; it is not a full enumeration
of infinite option sets. -/
  def approx (k : Nat) : OptionSet → List PreGame
  | .finite xs => xs
  | .nats => (List.range k).map PreGame.nat
  | .omegaPlusNats => (List.range k).map PreGame.omegaPlusNat
  | .omegaTimesTwoPlusNats => (List.range k).map PreGame.omegaTimesTwoPlusNat
  | .union a b => approx k a ++ approx k b

end OptionSet

/-! ## Bounded bridge into `SurrealCore.PreGame`

`toCore fuel` yields an executable finite approximation of a transfinite pre-game
in the existing finite `SurrealCore` carrier. Infinite option families are truncated
by `fuel`, and recursive descent also consumes `fuel`, giving a total definition.
-/

namespace CoreApprox

mutual
  /-- Bounded option-set reification into finite `SurrealCore` options. -/
  def toCoreOptionSet : Nat → OptionSet → List SurrealCore.PreGame
    | 0, _ => []
    | Nat.succ fuel, .finite xs => xs.map (toCore fuel)
    | Nat.succ fuel, .nats =>
        (List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.nat n))
    | Nat.succ fuel, .omegaPlusNats =>
        (List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.omegaPlusNat n))
    | Nat.succ fuel, .omegaTimesTwoPlusNats =>
        (List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.omegaTimesTwoPlusNat n))
    | Nat.succ fuel, .union a b =>
        toCoreOptionSet (Nat.succ fuel) a ++ toCoreOptionSet (Nat.succ fuel) b

  /-- Bounded game reification into finite `SurrealCore.PreGame`. -/
  def toCore : Nat → PreGame → SurrealCore.PreGame
    | 0, _ => SurrealCore.nullCut
    | Nat.succ fuel, .cut L R =>
        let Lc := toCoreOptionSet fuel L
        let Rc := toCoreOptionSet fuel R
        match Lc, Rc with
        | [], [] => SurrealCore.nullCut
        | _, _ => SurrealCore.PreGame.build Lc Rc
end

@[simp] theorem toCore_zeroFuel (g : PreGame) :
    toCore 0 g = SurrealCore.nullCut := by
  cases g
  simp [toCore]

@[simp] theorem toCore_succ_zero (fuel : Nat) :
    toCore (Nat.succ fuel) PreGame.zero = SurrealCore.nullCut := by
  cases fuel with
  | zero =>
      simp [PreGame.zero, toCore, toCoreOptionSet]
  | succ fuel =>
      simp [PreGame.zero, toCore, toCoreOptionSet]

@[simp] theorem toCore_nat_succ_birth_cases (fuel n : Nat) :
    (toCore (Nat.succ fuel) (PreGame.nat (Nat.succ n))).birth =
      match fuel with
      | 0 => 0
      | Nat.succ fuel' => Nat.succ ((toCore fuel' (PreGame.nat n)).birth) := by
  cases fuel with
  | zero =>
      simp [PreGame.nat, toCore, toCoreOptionSet, SurrealCore.nullCut]
  | succ fuel =>
      simp [PreGame.nat, toCore, toCoreOptionSet, SurrealCore.PreGame.build,
        SurrealCore.PreGame.maxBirth]

/-- Closed birthday form for bounded finite-nat approximants. -/
theorem toCore_nat_birth_eq_min_half_fuel (n fuel : Nat) :
    (toCore fuel (PreGame.nat n)).birth = Nat.min n (fuel / 2) := by
  induction n generalizing fuel with
  | zero =>
      cases fuel <;> simp [PreGame.nat, SurrealCore.nullCut]
  | succ n ih =>
      cases fuel with
      | zero =>
          simp [PreGame.nat, SurrealCore.nullCut]
      | succ fuel =>
          cases fuel with
          | zero =>
              simp [PreGame.nat, toCore, toCoreOptionSet, SurrealCore.nullCut]
          | succ fuel =>
              have hdiv : (Nat.succ (Nat.succ fuel)) / 2 = Nat.succ (fuel / 2) := by
                omega
              calc
                (toCore (Nat.succ (Nat.succ fuel)) (PreGame.nat (Nat.succ n))).birth
                    = Nat.succ ((toCore fuel (PreGame.nat n)).birth) := by
                        simp [toCore_nat_succ_birth_cases]
                _ = Nat.succ (Nat.min n (fuel / 2)) := by
                        rw [ih]
                _ = Nat.min (Nat.succ n) (Nat.succ (fuel / 2)) := by
                        simp [Nat.succ_min_succ]
                _ = Nat.min (Nat.succ n) ((Nat.succ (Nat.succ fuel)) / 2) := by
                        rw [hdiv]

/-- Fuel monotonicity for bounded finite-nat approximation birthdays. -/
theorem toCore_nat_birth_mono_fuel : ∀ n fuel,
    (toCore fuel (PreGame.nat n)).birth ≤ (toCore (Nat.succ fuel) (PreGame.nat n)).birth
  | n, fuel => by
      have hdiv : fuel / 2 ≤ (Nat.succ fuel) / 2 := by
        omega
      have hleft : Nat.min n (fuel / 2) ≤ n := Nat.min_le_left n (fuel / 2)
      have hright : Nat.min n (fuel / 2) ≤ (Nat.succ fuel) / 2 :=
        Nat.le_trans (Nat.min_le_right n (fuel / 2)) hdiv
      have hmin : Nat.min n (fuel / 2) ≤ Nat.min n ((Nat.succ fuel) / 2) :=
        (Nat.le_min).2 ⟨hleft, hright⟩
      simpa [toCore_nat_birth_eq_min_half_fuel] using hmin

theorem toCore_succ_succ_omega_birth_pos (fuel : Nat) :
    0 < (toCore (Nat.succ (Nat.succ fuel)) PreGame.omega).birth := by
  simp [PreGame.omega, toCore, toCoreOptionSet, SurrealCore.PreGame.build,
    SurrealCore.PreGame.maxBirth]

theorem toCore_succ_succ_omegaPlusNat_birth_pos (fuel n : Nat) :
    0 < (toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaPlusNat n)).birth := by
  cases n with
  | zero =>
      simpa [PreGame.omegaPlusNat] using toCore_succ_succ_omega_birth_pos fuel
  | succ n =>
      simp [PreGame.omegaPlusNat, toCore, toCoreOptionSet, SurrealCore.PreGame.build,
        SurrealCore.PreGame.maxBirth]

private theorem foldl_max_birth_le
    {n : Nat} :
    ∀ (xs : List SurrealCore.PreGame) (acc : Nat),
      acc ≤ n →
      (∀ g ∈ xs, g.birth ≤ n) →
      List.foldl (fun a g => Nat.max a g.birth) acc xs ≤ n
  | [], acc, hacc, _ => by
      simpa using hacc
  | x :: xs, acc, hacc, hxs => by
      have hx : x.birth ≤ n := hxs x (by simp)
      have hacc' : Nat.max acc x.birth ≤ n := (max_le_iff.2 ⟨hacc, hx⟩)
      exact foldl_max_birth_le xs (Nat.max acc x.birth) hacc' (by
        intro g hg
        exact hxs g (by simp [hg]))

private theorem foldl_max_birth_mono_acc :
    ∀ (xs : List SurrealCore.PreGame) (a b : Nat),
      a ≤ b →
      List.foldl (fun acc g => Nat.max acc g.birth) a xs ≤
        List.foldl (fun acc g => Nat.max acc g.birth) b xs
  | [], a, b, hab => by
      simpa using hab
  | x :: xs, a, b, hab => by
      have hstep : Nat.max a x.birth ≤ Nat.max b x.birth := max_le_max hab (le_rfl)
      exact foldl_max_birth_mono_acc xs (Nat.max a x.birth) (Nat.max b x.birth) hstep

private theorem foldl_max_birth_acc_le :
    ∀ (xs : List SurrealCore.PreGame) (acc : Nat),
      acc ≤ List.foldl (fun a g => Nat.max a g.birth) acc xs
  | [], acc => by
      simp
  | x :: xs, acc => by
      have hstep : acc ≤ Nat.max acc x.birth := Nat.le_max_left acc x.birth
      exact Nat.le_trans hstep (foldl_max_birth_acc_le xs (Nat.max acc x.birth))

private theorem maxBirth_le_of_forall {xs : List SurrealCore.PreGame} {n : Nat}
    (h : ∀ g ∈ xs, g.birth ≤ n) :
    SurrealCore.PreGame.maxBirth xs ≤ n := by
  unfold SurrealCore.PreGame.maxBirth
  simpa using foldl_max_birth_le (n := n) xs 0 (Nat.zero_le n) h

private theorem birth_le_maxBirth_of_mem
    {xs : List SurrealCore.PreGame} {g : SurrealCore.PreGame}
    (hg : g ∈ xs) :
    g.birth ≤ SurrealCore.PreGame.maxBirth xs := by
  unfold SurrealCore.PreGame.maxBirth
  induction xs generalizing g with
  | nil =>
      cases hg
  | cons x xs ih =>
      simp at hg
      cases hg with
      | inl hgx =>
          subst g
          have hacc :
              Nat.max 0 x.birth ≤
                List.foldl (fun a g => Nat.max a g.birth) (Nat.max 0 x.birth) xs :=
            foldl_max_birth_acc_le xs (Nat.max 0 x.birth)
          exact Nat.le_trans (Nat.le_max_right 0 x.birth) hacc
      | inr hgx =>
          have hbase :
              g.birth ≤ List.foldl (fun a g => Nat.max a g.birth) 0 xs := ih hgx
          have hmono :
              List.foldl (fun a g => Nat.max a g.birth) 0 xs ≤
                List.foldl (fun a g => Nat.max a g.birth) (Nat.max 0 x.birth) xs :=
            foldl_max_birth_mono_acc xs 0 (Nat.max 0 x.birth) (Nat.zero_le _)
          exact Nat.le_trans hbase hmono

private theorem maxBirth_range_nat_toCore_eq_half (fuel : Nat) :
    SurrealCore.PreGame.maxBirth
      ((List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.nat n))) = fuel / 2 := by
  let xs := (List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.nat n))
  have hupper : SurrealCore.PreGame.maxBirth xs ≤ fuel / 2 := by
    apply maxBirth_le_of_forall
    intro g hg
    rcases List.mem_map.1 hg with ⟨n, _, rfl⟩
    calc
      (toCore fuel (PreGame.nat n)).birth = Nat.min n (fuel / 2) :=
        toCore_nat_birth_eq_min_half_fuel n fuel
      _ ≤ fuel / 2 := Nat.min_le_right n (fuel / 2)
  have hmem : toCore fuel (PreGame.nat (fuel / 2)) ∈ xs := by
    dsimp [xs]
    refine List.mem_map.2 ?_
    refine ⟨fuel / 2, ?_, rfl⟩
    exact List.mem_range.2 (by omega)
  have hlower : fuel / 2 ≤ SurrealCore.PreGame.maxBirth xs := by
    have hbirth_le :
        (toCore fuel (PreGame.nat (fuel / 2))).birth ≤ SurrealCore.PreGame.maxBirth xs :=
      birth_le_maxBirth_of_mem hmem
    have hbirth :
        (toCore fuel (PreGame.nat (fuel / 2))).birth = fuel / 2 := by
      simp [toCore_nat_birth_eq_min_half_fuel]
    simpa [hbirth] using hbirth_le
  exact Nat.le_antisymm hupper hlower

/-- Closed birthday form for bounded `ω` approximants. -/
theorem toCore_omega_birth_eq_half_fuel (fuel : Nat) :
    (toCore fuel PreGame.omega).birth = fuel / 2 := by
  cases fuel with
  | zero =>
      simp [PreGame.omega, SurrealCore.nullCut]
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [PreGame.omega, toCore, toCoreOptionSet, SurrealCore.nullCut]
      | succ fuel =>
          let xs := (List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.nat n))
          have hxs_ne : xs ≠ [] := by
            dsimp [xs]
            simp
          have hcore :
              toCore (Nat.succ (Nat.succ fuel)) PreGame.omega =
                SurrealCore.PreGame.build xs [] := by
            simp [PreGame.omega, toCore, toCoreOptionSet, xs, hxs_ne]
          have hmax : SurrealCore.PreGame.maxBirth xs = fuel / 2 := by
            simpa [xs] using maxBirth_range_nat_toCore_eq_half fuel
          calc
            (toCore (Nat.succ (Nat.succ fuel)) PreGame.omega).birth
                = (SurrealCore.PreGame.build xs []).birth := by
                    simp [hcore]
            _ = Nat.succ (Nat.max (SurrealCore.PreGame.maxBirth xs) (SurrealCore.PreGame.maxBirth [])) := by
                  simp [SurrealCore.PreGame.build]
            _ = Nat.succ (SurrealCore.PreGame.maxBirth xs) := by
                  have hnil : SurrealCore.PreGame.maxBirth ([] : List SurrealCore.PreGame) = 0 := by
                    simp [SurrealCore.PreGame.maxBirth]
                  simp [hnil]
            _ = Nat.succ (fuel / 2) := by
                  rw [hmax]
            _ = (Nat.succ (Nat.succ fuel)) / 2 := by
                  omega

private theorem maxBirth_append_eq_of_left_eq_of_right_le
    {xs ys : List SurrealCore.PreGame} {m : Nat}
    (hxs : SurrealCore.PreGame.maxBirth xs = m)
    (hys : ∀ g ∈ ys, g.birth ≤ m) :
    SurrealCore.PreGame.maxBirth (xs ++ ys) = m := by
  have hupper : SurrealCore.PreGame.maxBirth (xs ++ ys) ≤ m := by
    apply maxBirth_le_of_forall
    intro g hg
    rcases List.mem_append.1 hg with hgx | hgy
    · have hbirth : g.birth ≤ SurrealCore.PreGame.maxBirth xs := birth_le_maxBirth_of_mem hgx
      simpa [hxs] using hbirth
    · exact hys g hgy
  have hlower : m ≤ SurrealCore.PreGame.maxBirth (xs ++ ys) := by
    calc
      m = SurrealCore.PreGame.maxBirth xs := by symm; exact hxs
      _ ≤ SurrealCore.PreGame.maxBirth (xs ++ ys) := by
            unfold SurrealCore.PreGame.maxBirth
            simpa [List.foldl_append] using
              foldl_max_birth_acc_le ys (List.foldl (fun a g => Nat.max a g.birth) 0 xs)
  exact Nat.le_antisymm hupper hlower

private theorem mem_omegaPlusNatList_exists :
    ∀ {m : Nat} {g : PreGame}, g ∈ PreGame.omegaPlusNatList m →
      ∃ k : Nat, k < m ∧ g = PreGame.omegaPlusNat k
  | 0, _, hg => by
      simp [PreGame.omegaPlusNatList] at hg
  | Nat.succ m, g, hg => by
      simp [PreGame.omegaPlusNatList] at hg
      rcases hg with rfl | hg
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · rcases mem_omegaPlusNatList_exists hg with ⟨k, hk, rfl⟩
        exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m), rfl⟩

private theorem mem_omegaTimesTwoPlusNatList_exists :
    ∀ {m : Nat} {g : PreGame}, g ∈ PreGame.omegaTimesTwoPlusNatList m →
      ∃ k : Nat, k < m ∧ g = PreGame.omegaTimesTwoPlusNat k
  | 0, _, hg => by
      simp [PreGame.omegaTimesTwoPlusNatList] at hg
  | Nat.succ m, g, hg => by
      simp [PreGame.omegaTimesTwoPlusNatList] at hg
      rcases hg with rfl | hg
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · rcases mem_omegaTimesTwoPlusNatList_exists hg with ⟨k, hk, rfl⟩
        exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m), rfl⟩

/-- Closed birthday form for bounded `ω+n` approximants: all finite offsets share
the same bounded depth profile as `ω`. -/
theorem toCore_omegaPlusNat_birth_eq_half_fuel (fuel n : Nat) :
    (toCore fuel (PreGame.omegaPlusNat n)).birth = fuel / 2 := by
  revert n
  refine Nat.strongRecOn fuel ?_
  intro fuel ih n
  cases fuel with
  | zero =>
      cases n <;> simp [PreGame.omegaPlusNat, SurrealCore.nullCut]
  | succ fuel =>
      cases fuel with
      | zero =>
          have hω : (toCore 1 PreGame.omega).birth = 0 := by
            simp [PreGame.omega, toCore, toCoreOptionSet, SurrealCore.nullCut]
          cases n with
          | zero =>
              simpa [PreGame.omegaPlusNat] using hω
          | succ n =>
              simp [PreGame.omegaPlusNat, toCore, toCoreOptionSet, SurrealCore.nullCut]
      | succ fuel =>
          cases n with
          | zero =>
              simpa [PreGame.omegaPlusNat] using
                toCore_omega_birth_eq_half_fuel (Nat.succ (Nat.succ fuel))
          | succ n =>
              let xsNat := (List.range (Nat.succ fuel)).map (fun k => toCore fuel (PreGame.nat k))
              let xsExtra := (PreGame.omegaPlusNatList (Nat.succ n)).map (toCore fuel)
              have hNat : SurrealCore.PreGame.maxBirth xsNat = fuel / 2 := by
                simpa [xsNat] using maxBirth_range_nat_toCore_eq_half fuel
              have hExtra : ∀ g ∈ xsExtra, g.birth ≤ fuel / 2 := by
                intro g hg
                rcases List.mem_map.1 hg with ⟨pg, hpg, rfl⟩
                rcases mem_omegaPlusNatList_exists hpg with ⟨k, hk, rfl⟩
                have hkFuel : fuel < Nat.succ (Nat.succ fuel) := by omega
                have hrec :
                    (toCore fuel (PreGame.omegaPlusNat k)).birth = fuel / 2 := ih fuel hkFuel k
                simp [hrec]
              have hmax : SurrealCore.PreGame.maxBirth (xsNat ++ xsExtra) = fuel / 2 :=
                maxBirth_append_eq_of_left_eq_of_right_le hNat hExtra
              have hnonempty : xsNat ++ xsExtra ≠ [] := by
                have hxsNat : xsNat ≠ [] := by
                  dsimp [xsNat]
                  simp
                intro h
                exact hxsNat (List.append_eq_nil_iff.1 h).1
              have hcore :
                  toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaPlusNat (Nat.succ n)) =
                    SurrealCore.PreGame.build (xsNat ++ xsExtra) [] := by
                simp [PreGame.omegaPlusNat, toCore, toCoreOptionSet, xsNat, xsExtra, hnonempty]
              calc
                (toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaPlusNat (Nat.succ n))).birth
                    = (SurrealCore.PreGame.build (xsNat ++ xsExtra) []).birth := by
                        simp [hcore]
                _ = Nat.succ (Nat.max (SurrealCore.PreGame.maxBirth (xsNat ++ xsExtra))
                    (SurrealCore.PreGame.maxBirth [])) := by
                      simp [SurrealCore.PreGame.build]
                _ = Nat.succ (SurrealCore.PreGame.maxBirth (xsNat ++ xsExtra)) := by
                      have hnil : SurrealCore.PreGame.maxBirth ([] : List SurrealCore.PreGame) = 0 := by
                        simp [SurrealCore.PreGame.maxBirth]
                      simp [hnil]
                _ = Nat.succ (fuel / 2) := by
                      rw [hmax]
                _ = (Nat.succ (Nat.succ fuel)) / 2 := by
                      omega

/-- Closed birthday form for bounded `ω+ω+n` approximants: all finite offsets share
the same bounded depth profile as `ω`. -/
theorem toCore_omegaTimesTwoPlusNat_birth_eq_half_fuel (fuel n : Nat) :
    (toCore fuel (PreGame.omegaTimesTwoPlusNat n)).birth = fuel / 2 := by
  revert n
  refine Nat.strongRecOn fuel ?_
  intro fuel ih n
  cases fuel with
  | zero =>
      cases n <;> simp [PreGame.omegaTimesTwoPlusNat, SurrealCore.nullCut]
  | succ fuel =>
      cases fuel with
      | zero =>
          cases n with
          | zero =>
              simp [PreGame.omegaTimesTwoPlusNat, PreGame.omegaTimesTwo, toCore, toCoreOptionSet,
                SurrealCore.nullCut]
          | succ n =>
              simp [PreGame.omegaTimesTwoPlusNat, toCore, toCoreOptionSet, SurrealCore.nullCut]
      | succ fuel =>
          cases n with
          | zero =>
              let xs := (List.range (Nat.succ fuel)).map (fun k => toCore fuel (PreGame.omegaPlusNat k))
              have hxs_ne : xs ≠ [] := by
                dsimp [xs]
                simp
              have hcore :
                  toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaTimesTwoPlusNat 0) =
                    SurrealCore.PreGame.build xs [] := by
                simp [PreGame.omegaTimesTwoPlusNat, PreGame.omegaTimesTwo, toCore, toCoreOptionSet, xs, hxs_ne]
              have hmax : SurrealCore.PreGame.maxBirth xs = fuel / 2 := by
                have hupper : SurrealCore.PreGame.maxBirth xs ≤ fuel / 2 := by
                  apply maxBirth_le_of_forall
                  intro g hg
                  rcases List.mem_map.1 hg with ⟨k, _, rfl⟩
                  calc
                    (toCore fuel (PreGame.omegaPlusNat k)).birth = fuel / 2 :=
                      toCore_omegaPlusNat_birth_eq_half_fuel fuel k
                    _ ≤ fuel / 2 := le_rfl
                have hmem : toCore fuel (PreGame.omegaPlusNat 0) ∈ xs := by
                  dsimp [xs]
                  refine List.mem_map.2 ?_
                  refine ⟨0, ?_, rfl⟩
                  exact List.mem_range.2 (Nat.succ_pos _)
                have hlower : fuel / 2 ≤ SurrealCore.PreGame.maxBirth xs := by
                  have hbirth_le :
                      (toCore fuel (PreGame.omegaPlusNat 0)).birth ≤ SurrealCore.PreGame.maxBirth xs :=
                    birth_le_maxBirth_of_mem hmem
                  have hbirth : (toCore fuel (PreGame.omegaPlusNat 0)).birth = fuel / 2 := by
                    simpa using toCore_omegaPlusNat_birth_eq_half_fuel fuel 0
                  simpa [hbirth] using hbirth_le
                exact Nat.le_antisymm hupper hlower
              calc
                (toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaTimesTwoPlusNat 0)).birth
                    = (SurrealCore.PreGame.build xs []).birth := by
                        simp [hcore]
                _ = Nat.succ (Nat.max (SurrealCore.PreGame.maxBirth xs) (SurrealCore.PreGame.maxBirth [])) := by
                      simp [SurrealCore.PreGame.build]
                _ = Nat.succ (SurrealCore.PreGame.maxBirth xs) := by
                      have hnil : SurrealCore.PreGame.maxBirth ([] : List SurrealCore.PreGame) = 0 := by
                        simp [SurrealCore.PreGame.maxBirth]
                      simp [hnil]
                _ = Nat.succ (fuel / 2) := by
                      rw [hmax]
                _ = (Nat.succ (Nat.succ fuel)) / 2 := by
                      omega
          | succ n =>
              let xsNat := (List.range (Nat.succ fuel)).map (fun k => toCore fuel (PreGame.nat k))
              let xsOmega := (List.range (Nat.succ fuel)).map (fun k => toCore fuel (PreGame.omegaPlusNat k))
              let xsExtra := (PreGame.omegaTimesTwoPlusNatList (Nat.succ n)).map (toCore fuel)
              have hNat : SurrealCore.PreGame.maxBirth xsNat = fuel / 2 := by
                simpa [xsNat] using maxBirth_range_nat_toCore_eq_half fuel
              have hOmega : ∀ g ∈ xsOmega, g.birth ≤ fuel / 2 := by
                intro g hg
                rcases List.mem_map.1 hg with ⟨k, _, rfl⟩
                simp [toCore_omegaPlusNat_birth_eq_half_fuel]
              have hExtra : ∀ g ∈ xsExtra, g.birth ≤ fuel / 2 := by
                intro g hg
                rcases List.mem_map.1 hg with ⟨pg, hpg, rfl⟩
                rcases mem_omegaTimesTwoPlusNatList_exists hpg with ⟨k, hk, rfl⟩
                have hkFuel : fuel < Nat.succ (Nat.succ fuel) := by omega
                have hrec :
                    (toCore fuel (PreGame.omegaTimesTwoPlusNat k)).birth = fuel / 2 := ih fuel hkFuel k
                simp [hrec]
              have hRest : ∀ g ∈ (xsOmega ++ xsExtra), g.birth ≤ fuel / 2 := by
                intro g hg
                rcases List.mem_append.1 hg with hgo | hge
                · exact hOmega g hgo
                · exact hExtra g hge
              have hmax :
                  SurrealCore.PreGame.maxBirth (xsNat ++ (xsOmega ++ xsExtra)) = fuel / 2 :=
                maxBirth_append_eq_of_left_eq_of_right_le hNat hRest
              have hnonempty : xsNat ++ (xsOmega ++ xsExtra) ≠ [] := by
                have hxsNat : xsNat ≠ [] := by
                  dsimp [xsNat]
                  simp
                intro h
                exact hxsNat (List.append_eq_nil_iff.1 h).1
              have hcore :
                  toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaTimesTwoPlusNat (Nat.succ n)) =
                    SurrealCore.PreGame.build (xsNat ++ (xsOmega ++ xsExtra)) [] := by
                simp [PreGame.omegaTimesTwoPlusNat, toCore, toCoreOptionSet, xsNat, xsOmega, xsExtra,
                  hnonempty]
              calc
                (toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaTimesTwoPlusNat (Nat.succ n))).birth
                    = (SurrealCore.PreGame.build (xsNat ++ (xsOmega ++ xsExtra)) []).birth := by
                        simp [hcore]
                _ = Nat.succ (Nat.max (SurrealCore.PreGame.maxBirth (xsNat ++ (xsOmega ++ xsExtra)))
                    (SurrealCore.PreGame.maxBirth [])) := by
                      simp [SurrealCore.PreGame.build]
                _ = Nat.succ (SurrealCore.PreGame.maxBirth (xsNat ++ (xsOmega ++ xsExtra))) := by
                      have hnil : SurrealCore.PreGame.maxBirth ([] : List SurrealCore.PreGame) = 0 := by
                        simp [SurrealCore.PreGame.maxBirth]
                      simp [hnil]
                _ = Nat.succ (fuel / 2) := by
                      rw [hmax]
                _ = (Nat.succ (Nat.succ fuel)) / 2 := by
                      omega

private theorem maxBirth_range_omegaPlusNat_toCore_eq_half (fuel : Nat) :
    SurrealCore.PreGame.maxBirth
      ((List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.omegaPlusNat n))) = fuel / 2 := by
  let xs := (List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.omegaPlusNat n))
  have hupper : SurrealCore.PreGame.maxBirth xs ≤ fuel / 2 := by
    apply maxBirth_le_of_forall
    intro g hg
    rcases List.mem_map.1 hg with ⟨n, _, rfl⟩
    calc
      (toCore fuel (PreGame.omegaPlusNat n)).birth = fuel / 2 :=
        toCore_omegaPlusNat_birth_eq_half_fuel fuel n
      _ ≤ fuel / 2 := le_rfl
  have hmem : toCore fuel (PreGame.omegaPlusNat 0) ∈ xs := by
    dsimp [xs]
    refine List.mem_map.2 ?_
    refine ⟨0, ?_, rfl⟩
    exact List.mem_range.2 (Nat.succ_pos _)
  have hlower : fuel / 2 ≤ SurrealCore.PreGame.maxBirth xs := by
    have hbirth_le :
        (toCore fuel (PreGame.omegaPlusNat 0)).birth ≤ SurrealCore.PreGame.maxBirth xs :=
      birth_le_maxBirth_of_mem hmem
    have hbirth : (toCore fuel (PreGame.omegaPlusNat 0)).birth = fuel / 2 := by
      simpa using toCore_omegaPlusNat_birth_eq_half_fuel fuel 0
    simpa [hbirth] using hbirth_le
  exact Nat.le_antisymm hupper hlower

private theorem maxBirth_range_omegaTimesTwoPlusNat_toCore_eq_half (fuel : Nat) :
    SurrealCore.PreGame.maxBirth
      ((List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.omegaTimesTwoPlusNat n)))
      = fuel / 2 := by
  let xs := (List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.omegaTimesTwoPlusNat n))
  have hupper : SurrealCore.PreGame.maxBirth xs ≤ fuel / 2 := by
    apply maxBirth_le_of_forall
    intro g hg
    rcases List.mem_map.1 hg with ⟨n, _, rfl⟩
    calc
      (toCore fuel (PreGame.omegaTimesTwoPlusNat n)).birth = fuel / 2 :=
        toCore_omegaTimesTwoPlusNat_birth_eq_half_fuel fuel n
      _ ≤ fuel / 2 := le_rfl
  have hmem : toCore fuel (PreGame.omegaTimesTwoPlusNat 0) ∈ xs := by
    dsimp [xs]
    refine List.mem_map.2 ?_
    refine ⟨0, ?_, rfl⟩
    exact List.mem_range.2 (Nat.succ_pos _)
  have hlower : fuel / 2 ≤ SurrealCore.PreGame.maxBirth xs := by
    have hbirth_le :
        (toCore fuel (PreGame.omegaTimesTwoPlusNat 0)).birth ≤ SurrealCore.PreGame.maxBirth xs :=
      birth_le_maxBirth_of_mem hmem
    have hbirth : (toCore fuel (PreGame.omegaTimesTwoPlusNat 0)).birth = fuel / 2 := by
      simpa using toCore_omegaTimesTwoPlusNat_birth_eq_half_fuel fuel 0
    simpa [hbirth] using hbirth_le
  exact Nat.le_antisymm hupper hlower

/-- Closed birthday form for bounded `ω+ω` approximants. -/
theorem toCore_omegaTimesTwo_birth_eq_half_fuel (fuel : Nat) :
    (toCore fuel PreGame.omegaTimesTwo).birth = fuel / 2 := by
  cases fuel with
  | zero =>
      simp [PreGame.omegaTimesTwo, SurrealCore.nullCut]
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [PreGame.omegaTimesTwo, toCore, toCoreOptionSet, SurrealCore.nullCut]
      | succ fuel =>
          let xs := (List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.omegaPlusNat n))
          have hxs_ne : xs ≠ [] := by
            dsimp [xs]
            simp
          have hcore :
              toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesTwo =
                SurrealCore.PreGame.build xs [] := by
            simp [PreGame.omegaTimesTwo, toCore, toCoreOptionSet, xs, hxs_ne]
          have hmax : SurrealCore.PreGame.maxBirth xs = fuel / 2 := by
            simpa [xs] using maxBirth_range_omegaPlusNat_toCore_eq_half fuel
          calc
            (toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesTwo).birth
                = (SurrealCore.PreGame.build xs []).birth := by
                    simp [hcore]
            _ = Nat.succ (Nat.max (SurrealCore.PreGame.maxBirth xs) (SurrealCore.PreGame.maxBirth [])) := by
                  simp [SurrealCore.PreGame.build]
            _ = Nat.succ (SurrealCore.PreGame.maxBirth xs) := by
                  have hnil : SurrealCore.PreGame.maxBirth ([] : List SurrealCore.PreGame) = 0 := by
                    simp [SurrealCore.PreGame.maxBirth]
                  simp [hnil]
            _ = Nat.succ (fuel / 2) := by
                  rw [hmax]
            _ = (Nat.succ (Nat.succ fuel)) / 2 := by
                  omega

/-- Closed birthday form for bounded `ω+ω+ω` approximants. -/
theorem toCore_omegaTimesThree_birth_eq_half_fuel (fuel : Nat) :
    (toCore fuel PreGame.omegaTimesThree).birth = fuel / 2 := by
  cases fuel with
  | zero =>
      simp [PreGame.omegaTimesThree, SurrealCore.nullCut]
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [PreGame.omegaTimesThree, toCore, toCoreOptionSet, SurrealCore.nullCut]
      | succ fuel =>
          let xs := (List.range (Nat.succ fuel)).map (fun n => toCore fuel (PreGame.omegaTimesTwoPlusNat n))
          have hxs_ne : xs ≠ [] := by
            dsimp [xs]
            simp
          have hcore :
              toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesThree =
                SurrealCore.PreGame.build xs [] := by
            simp [PreGame.omegaTimesThree, toCore, toCoreOptionSet, xs, hxs_ne]
          have hmax : SurrealCore.PreGame.maxBirth xs = fuel / 2 := by
            simpa [xs] using maxBirth_range_omegaTimesTwoPlusNat_toCore_eq_half fuel
          calc
            (toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesThree).birth
                = (SurrealCore.PreGame.build xs []).birth := by
                    simp [hcore]
            _ = Nat.succ (Nat.max (SurrealCore.PreGame.maxBirth xs) (SurrealCore.PreGame.maxBirth [])) := by
                  simp [SurrealCore.PreGame.build]
            _ = Nat.succ (SurrealCore.PreGame.maxBirth xs) := by
                  have hnil : SurrealCore.PreGame.maxBirth ([] : List SurrealCore.PreGame) = 0 := by
                    simp [SurrealCore.PreGame.maxBirth]
                  simp [hnil]
            _ = Nat.succ (fuel / 2) := by
                  rw [hmax]
            _ = (Nat.succ (Nat.succ fuel)) / 2 := by
                  omega

/-- Fuel monotonicity for bounded `ω` approximation birthdays. -/
theorem toCore_omega_birth_mono_fuel (fuel : Nat) :
    (toCore fuel PreGame.omega).birth ≤ (toCore (Nat.succ fuel) PreGame.omega).birth := by
  have hdiv : fuel / 2 ≤ (Nat.succ fuel) / 2 := by
    omega
  simpa [toCore_omega_birth_eq_half_fuel] using hdiv

/-- Fuel monotonicity for bounded `ω+n` approximation birthdays. -/
theorem toCore_omegaPlusNat_birth_mono_fuel (fuel n : Nat) :
    (toCore fuel (PreGame.omegaPlusNat n)).birth ≤
      (toCore (Nat.succ fuel) (PreGame.omegaPlusNat n)).birth := by
  have hdiv : fuel / 2 ≤ (Nat.succ fuel) / 2 := by
    omega
  simpa [toCore_omegaPlusNat_birth_eq_half_fuel] using hdiv

/-- Fuel monotonicity for bounded `ω+ω` approximation birthdays. -/
theorem toCore_omegaTimesTwo_birth_mono_fuel (fuel : Nat) :
    (toCore fuel PreGame.omegaTimesTwo).birth ≤
      (toCore (Nat.succ fuel) PreGame.omegaTimesTwo).birth := by
  have hdiv : fuel / 2 ≤ (Nat.succ fuel) / 2 := by
    omega
  simpa [toCore_omegaTimesTwo_birth_eq_half_fuel] using hdiv

/-- Fuel monotonicity for bounded `ω+ω+n` approximation birthdays. -/
theorem toCore_omegaTimesTwoPlusNat_birth_mono_fuel (fuel n : Nat) :
    (toCore fuel (PreGame.omegaTimesTwoPlusNat n)).birth ≤
      (toCore (Nat.succ fuel) (PreGame.omegaTimesTwoPlusNat n)).birth := by
  have hdiv : fuel / 2 ≤ (Nat.succ fuel) / 2 := by
    omega
  simpa [toCore_omegaTimesTwoPlusNat_birth_eq_half_fuel] using hdiv

/-- Fuel monotonicity for bounded `ω+ω+ω` approximation birthdays. -/
theorem toCore_omegaTimesThree_birth_mono_fuel (fuel : Nat) :
    (toCore fuel PreGame.omegaTimesThree).birth ≤
      (toCore (Nat.succ fuel) PreGame.omegaTimesThree).birth := by
  have hdiv : fuel / 2 ≤ (Nat.succ fuel) / 2 := by
    omega
  simpa [toCore_omegaTimesThree_birth_eq_half_fuel] using hdiv

/-- Bounded approximation birthdays are finite-offset invariant on the `ω+n` family. -/
theorem toCore_omegaPlusNat_birth_eq_omega_birth (fuel n : Nat) :
    (toCore fuel (PreGame.omegaPlusNat n)).birth = (toCore fuel PreGame.omega).birth := by
  simp [toCore_omegaPlusNat_birth_eq_half_fuel, toCore_omega_birth_eq_half_fuel]

/-- Bounded `ω+ω` approximation birthdays match bounded `ω` birthdays. -/
theorem toCore_omegaTimesTwo_birth_eq_omega_birth (fuel : Nat) :
    (toCore fuel PreGame.omegaTimesTwo).birth = (toCore fuel PreGame.omega).birth := by
  simp [toCore_omegaTimesTwo_birth_eq_half_fuel, toCore_omega_birth_eq_half_fuel]

/-- Bounded approximation birthdays are finite-offset invariant on the `ω+ω+n` family. -/
theorem toCore_omegaTimesTwoPlusNat_birth_eq_omega_birth (fuel n : Nat) :
    (toCore fuel (PreGame.omegaTimesTwoPlusNat n)).birth = (toCore fuel PreGame.omega).birth := by
  simp [toCore_omegaTimesTwoPlusNat_birth_eq_half_fuel, toCore_omega_birth_eq_half_fuel]

/-- Bounded `ω+ω+ω` approximation birthdays match bounded `ω` birthdays. -/
theorem toCore_omegaTimesThree_birth_eq_omega_birth (fuel : Nat) :
    (toCore fuel PreGame.omegaTimesThree).birth = (toCore fuel PreGame.omega).birth := by
  simp [toCore_omegaTimesThree_birth_eq_half_fuel, toCore_omega_birth_eq_half_fuel]

mutual
  /-- Every option produced by `toCoreOptionSet fuel` has birthday bounded by `fuel`. -/
  theorem mem_toCoreOptionSet_birth_le :
      ∀ fuel opts g, g ∈ toCoreOptionSet fuel opts → g.birth ≤ fuel
    | 0, _, _, hg => by
        simp [toCoreOptionSet] at hg
    | Nat.succ fuel, .finite xs, g, hg => by
        simp [toCoreOptionSet] at hg
        rcases hg with ⟨x, _, rfl⟩
        exact Nat.le_succ_of_le (toCore_birth_le fuel x)
    | Nat.succ fuel, .nats, g, hg => by
        simp [toCoreOptionSet] at hg
        rcases hg with ⟨n, _, rfl⟩
        exact Nat.le_succ_of_le (toCore_birth_le fuel (PreGame.nat n))
    | Nat.succ fuel, .omegaPlusNats, g, hg => by
        simp [toCoreOptionSet] at hg
        rcases hg with ⟨n, _, rfl⟩
        exact Nat.le_succ_of_le (toCore_birth_le fuel (PreGame.omegaPlusNat n))
    | Nat.succ fuel, .omegaTimesTwoPlusNats, g, hg => by
        simp [toCoreOptionSet] at hg
        rcases hg with ⟨n, _, rfl⟩
        exact Nat.le_succ_of_le (toCore_birth_le fuel (PreGame.omegaTimesTwoPlusNat n))
    | Nat.succ fuel, .union a b, g, hg => by
        simp [toCoreOptionSet] at hg
        rcases hg with hga | hgb
        · exact mem_toCoreOptionSet_birth_le (Nat.succ fuel) a g hga
        · exact mem_toCoreOptionSet_birth_le (Nat.succ fuel) b g hgb

  /-- Bounded reification preserves a birthday upper-bound by fuel. -/
  theorem toCore_birth_le :
      ∀ fuel g, (toCore fuel g).birth ≤ fuel
    | 0, _ => by
        simp [SurrealCore.nullCut]
    | Nat.succ fuel, .cut L R => by
        have hL : ∀ g ∈ toCoreOptionSet fuel L, g.birth ≤ fuel := by
          intro g hg
          exact mem_toCoreOptionSet_birth_le fuel L g hg
        have hR : ∀ g ∈ toCoreOptionSet fuel R, g.birth ≤ fuel := by
          intro g hg
          exact mem_toCoreOptionSet_birth_le fuel R g hg
        have hmaxL : SurrealCore.PreGame.maxBirth (toCoreOptionSet fuel L) ≤ fuel :=
          maxBirth_le_of_forall hL
        have hmaxR : SurrealCore.PreGame.maxBirth (toCoreOptionSet fuel R) ≤ fuel :=
          maxBirth_le_of_forall hR
        have hmax :
            Nat.max
              (SurrealCore.PreGame.maxBirth (toCoreOptionSet fuel L))
              (SurrealCore.PreGame.maxBirth (toCoreOptionSet fuel R)) ≤ fuel :=
          max_le_iff.2 ⟨hmaxL, hmaxR⟩
        cases hLset : toCoreOptionSet fuel L <;> cases hRset : toCoreOptionSet fuel R
        · simp [toCore, hLset, hRset, SurrealCore.nullCut]
        · simpa [toCore, hLset, hRset, SurrealCore.PreGame.build] using Nat.succ_le_succ hmax
        · simpa [toCore, hLset, hRset, SurrealCore.PreGame.build] using Nat.succ_le_succ hmax
        · simpa [toCore, hLset, hRset, SurrealCore.PreGame.build] using Nat.succ_le_succ hmax
end

theorem toCore_succ_succ_omega_birth_bounds (fuel : Nat) :
    1 ≤ (toCore (Nat.succ (Nat.succ fuel)) PreGame.omega).birth ∧
      (toCore (Nat.succ (Nat.succ fuel)) PreGame.omega).birth ≤ Nat.succ (Nat.succ fuel) := by
  refine ⟨Nat.succ_le_of_lt (toCore_succ_succ_omega_birth_pos fuel), ?_⟩
  exact toCore_birth_le (Nat.succ (Nat.succ fuel)) PreGame.omega

theorem toCore_succ_succ_omegaPlusNat_birth_bounds (fuel n : Nat) :
    1 ≤ (toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaPlusNat n)).birth ∧
      (toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaPlusNat n)).birth ≤ Nat.succ (Nat.succ fuel) := by
  refine ⟨Nat.succ_le_of_lt (toCore_succ_succ_omegaPlusNat_birth_pos fuel n), ?_⟩
  exact toCore_birth_le (Nat.succ (Nat.succ fuel)) (PreGame.omegaPlusNat n)

theorem toCore_succ_succ_omegaTimesTwo_birth_pos (fuel : Nat) :
    0 < (toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesTwo).birth := by
  have hbirth :
      (toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesTwo).birth =
        (Nat.succ (Nat.succ fuel)) / 2 := by
    simpa using toCore_omegaTimesTwo_birth_eq_half_fuel (Nat.succ (Nat.succ fuel))
  rw [hbirth]
  omega

theorem toCore_succ_succ_omegaTimesTwo_birth_bounds (fuel : Nat) :
    1 ≤ (toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesTwo).birth ∧
      (toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesTwo).birth ≤ Nat.succ (Nat.succ fuel) := by
  refine ⟨Nat.succ_le_of_lt (toCore_succ_succ_omegaTimesTwo_birth_pos fuel), ?_⟩
  exact toCore_birth_le (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesTwo

theorem toCore_succ_succ_omegaTimesThree_birth_pos (fuel : Nat) :
    0 < (toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesThree).birth := by
  have hbirth :
      (toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesThree).birth =
        (Nat.succ (Nat.succ fuel)) / 2 := by
    simpa using toCore_omegaTimesThree_birth_eq_half_fuel (Nat.succ (Nat.succ fuel))
  rw [hbirth]
  omega

theorem toCore_succ_succ_omegaTimesThree_birth_bounds (fuel : Nat) :
    1 ≤ (toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesThree).birth ∧
      (toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesThree).birth ≤ Nat.succ (Nat.succ fuel) := by
  refine ⟨Nat.succ_le_of_lt (toCore_succ_succ_omegaTimesThree_birth_pos fuel), ?_⟩
  exact toCore_birth_le (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesThree

end CoreApprox

end TransfinitePreGame

end Surreal
end Numbers
end HeytingLean
