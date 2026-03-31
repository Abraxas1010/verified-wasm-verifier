/-!
# Crypto Algorithm Registry ("diamond")

Lean-level model of the crypto‑agility diamond and simple invariants:
- A registry of algorithm IDs/versions for {hash, signature, commitment, proof}.
- Rotation windows for controlled migrations (old ∪ new during grace).
- Meaning‑over‑mechanism: validity depends only on pinned bytes + ordered
  statement fields; the chosen algorithm label does not alter the predicate.
-/

namespace HeytingLean
namespace Crypto
namespace AlgRegistry

/-! ## Algorithm identifiers and registry entries -/

structure AlgId where
  name    : String
  version : String
  deriving DecidableEq, Repr, Inhabited

structure Diamond where
  hash       : AlgId
  signature  : AlgId
  commitment : AlgId
  proof      : AlgId
  deriving DecidableEq, Repr

/-- A point-in-time registry (e.g., epoch-based). -/
structure Entry where
  epoch   : Nat
  diamond : Diamond
  deriving DecidableEq, Repr

/-! ## Rotation windows (per-algorithm) -/

structure Rotation where
  old : AlgId
  new : AlgId
  t0  : Nat  -- start of grace window (inclusive)
  t1  : Nat  -- end of grace window (inclusive)
  deriving DecidableEq, Repr

/-- Acceptance predicate for a rotation window. -/
def accepts (rot : Rotation) (t : Nat) (a : AlgId) : Prop :=
  (t < rot.t0 ∧ a = rot.old) ∨
  (rot.t0 ≤ t ∧ t ≤ rot.t1 ∧ (a = rot.old ∨ a = rot.new)) ∨
  (rot.t1 < t ∧ a = rot.new)

-- Rotation window acceptance is defined by three disjoint regimes. Additional
-- formal properties (e.g., exclusivity under t0 ≤ t1) can be layered here as needed.

/-- Well-formed rotation window (t0 ≤ t1). -/
def WellFormed (rot : Rotation) : Prop := rot.t0 ≤ rot.t1

/-- Before the grace window, only `old` is accepted. -/
theorem before_iff_old {rot : Rotation} (wf : WellFormed rot)
    {t : Nat} (ht : t < rot.t0) {a : AlgId} :
    accepts rot t a ↔ a = rot.old := by
  constructor
  · intro h
    rcases h with h₁ | h₂ | h₃
    · exact h₁.2
    ·
      have : rot.t0 < rot.t0 := Nat.lt_of_le_of_lt h₂.1 ht
      exact (Nat.lt_irrefl _ this).elim
    ·
      have t_le_t1 : t ≤ rot.t1 := Nat.le_trans (Nat.le_of_lt ht) wf
      have : rot.t1 < rot.t1 := Nat.lt_of_lt_of_le h₃.1 t_le_t1
      exact (Nat.lt_irrefl _ this).elim
  · intro ha; subst ha; exact Or.inl ⟨ht, rfl⟩

/-- During the grace window, both `old` and `new` are accepted, and no others. -/
theorem during_iff_old_or_new {rot : Rotation}
    {t : Nat} (ht0 : rot.t0 ≤ t) (ht1 : t ≤ rot.t1) {a : AlgId} :
    accepts rot t a ↔ a = rot.old ∨ a = rot.new := by
  constructor
  · intro h
    rcases h with h₁ | h₂ | h₃
    ·
      have : t < t := Nat.lt_of_lt_of_le h₁.1 ht0
      exact (Nat.lt_irrefl _ this).elim
    · exact h₂.2.2
    ·
      have : t < t := Nat.lt_of_le_of_lt ht1 h₃.1
      exact (Nat.lt_irrefl _ this).elim
  · intro ha
    exact Or.inr (Or.inl ⟨ht0, ht1, ha⟩)

/-- After the grace window, only `new` is accepted. -/
theorem after_iff_new {rot : Rotation} (wf : WellFormed rot)
    {t : Nat} (ht : rot.t1 < t) {a : AlgId} :
    accepts rot t a ↔ a = rot.new := by
  constructor
  · intro h
    rcases h with h₁ | h₂ | h₃
    ·
      have t1_lt_t0 : rot.t1 < rot.t0 := Nat.lt_trans ht h₁.1
      have : rot.t1 < rot.t1 := Nat.lt_of_lt_of_le t1_lt_t0 wf
      exact (Nat.lt_irrefl _ this).elim
    ·
      have : t < t := Nat.lt_of_le_of_lt h₂.2.1 ht
      exact (Nat.lt_irrefl _ this).elim
    · exact h₃.2
  · intro ha; subst ha; exact Or.inr (Or.inr ⟨ht, rfl⟩)

/-! ## Meaning-over-mechanism (spec) -/

structure ReceiptView where
  canonical_semantics_hash : String
  compiled_system_hash     : String
  stmtHash                 : String
  deriving DecidableEq, Repr

/-- Validity predicate that depends only on pinned bytes + stmt hash. -/
def valid (rv : ReceiptView)
    (canon compiled stmt : String) : Prop :=
  rv.canonical_semantics_hash = canon ∧
  rv.compiled_system_hash = compiled ∧
  rv.stmtHash = stmt

/-- If two contexts produce the same pinned bytes and stmt hash, validity is the same,
    regardless of the algorithm labels in the registry (meaning over mechanism). -/
theorem meaning_over_mechanism (rv : ReceiptView)
    {canon compiled stmt : String} {canon' compiled' stmt' : String}
    (hC : canon = canon') (hS : compiled = compiled') (hT : stmt = stmt') :
    valid rv canon compiled stmt ↔ valid rv canon' compiled' stmt' := by
  cases rv
  cases hC
  cases hS
  cases hT
  simp [valid]

end AlgRegistry
end Crypto
end HeytingLean
