import Mathlib.Order.Sublocale

/-!
# Nucleus ratchet: ordering and fixed-point inclusion

Mathlib orders nuclei pointwise (`Nucleus X` is a complete lattice when `X` is),
while sublocales are ordered by inclusion. The fixed-point carrier of a nucleus is `toSublocale`.

Key fact (Mathlib): `m.toSublocale ≤ n.toSublocale ↔ n ≤ m`.

This file packages the corresponding “ratchet” direction: tightening a nucleus yields a smaller
fixed-point core.
-/

namespace HeytingLean
namespace CPP

universe u

variable {X : Type u} [Order.Frame X]

theorem toSublocale_antitone {m n : Nucleus X} (h : m ≤ n) :
    n.toSublocale ≤ m.toSublocale :=
  (Nucleus.toSublocale_le_toSublocale).2 h

/-- Inclusion map between Ω-cores induced by an inequality of nuclei. -/
def omegaMap {m n : Nucleus X} (h : m ≤ n) :
    n.toSublocale → m.toSublocale :=
  fun x => ⟨x.1, toSublocale_antitone (m := m) (n := n) h x.2⟩

@[simp] lemma omegaMap_coe {m n : Nucleus X} (h : m ≤ n) (x : n.toSublocale) :
    ((omegaMap (m := m) (n := n) h x : m.toSublocale) : X) = (x : X) :=
  rfl

end CPP
end HeytingLean

