import HeytingLean.IteratedVirtual.NGlobular

/-!
# IteratedVirtual.GlobeN

Walking `n`-globes as **truncated** globular sets `NGlobularSet n`.

Model:
- for dimensions `< n`, there are two boundary cells (`Fin 2`);
- for dimensions `≥ n`, there is a single cell (`PUnit`).

Everything is `ULift`ed so the construction works uniformly in any universe `u`.
-/

namespace HeytingLean
namespace IteratedVirtual

universe u

namespace GlobeN

def Cell (n : Nat) (k : Nat) : Type u :=
  ULift (if k < n then Fin 2 else PUnit)

private def boundary0 : ULift (Fin 2) := ULift.up (⟨0, by decide⟩ : Fin 2)
private def boundary1 : ULift (Fin 2) := ULift.up (⟨1, by decide⟩ : Fin 2)

def src (n : Nat) (k : Nat) (hk : k < n) : Cell n (k + 1) → Cell n k := by
  intro _
  have hk' : k < n := hk
  -- Codomain is on the `< n` branch, so it is `ULift (Fin 2)`.
  simpa [Cell, hk'] using boundary0

def tgt (n : Nat) (k : Nat) (hk : k < n) : Cell n (k + 1) → Cell n k := by
  intro _
  have hk' : k < n := hk
  simpa [Cell, hk'] using boundary1

theorem src_src_eq_src_tgt (n : Nat) (k : Nat) (hk0 : k < n) (hk1 : k + 1 < n) (x : Cell n (k + 2)) :
    src n k hk0 (src n (k + 1) hk1 x) =
      src n k hk0 (tgt n (k + 1) hk1 x) := by
  simp [src]

theorem tgt_src_eq_tgt_tgt (n : Nat) (k : Nat) (hk0 : k < n) (hk1 : k + 1 < n) (x : Cell n (k + 2)) :
    tgt n k hk0 (src n (k + 1) hk1 x) =
      tgt n k hk0 (tgt n (k + 1) hk1 x) := by
  simp [tgt]

end GlobeN

def GlobeN (n : Nat) : NGlobularSet n where
  Cell := GlobeN.Cell n
  src := fun k hk => GlobeN.src n k hk
  tgt := fun k hk => GlobeN.tgt n k hk
  src_src_eq_src_tgt := fun k hk0 hk1 x => GlobeN.src_src_eq_src_tgt n k hk0 hk1 x
  tgt_src_eq_tgt_tgt := fun k hk0 hk1 x => GlobeN.tgt_src_eq_tgt_tgt n k hk0 hk1 x

end IteratedVirtual
end HeytingLean
