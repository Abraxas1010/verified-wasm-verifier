import HeytingLean.Crypto.CoreSemantics
import HeytingLean.Crypto.Compile
import HeytingLean.Crypto.Lens.Transport

namespace HeytingLean
namespace Crypto

open HeytingLean.LoF

universe u v

variable {α : Type u} [PrimaryAlgebra α]
variable {R : Reentry α}

namespace Lens

variable (L : Lens (R := R))

def canonicalRun {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) :
    Trace L × L.Carrier :=
  run L (Form.compile φ) (fun i => L.enc (ρ i))

def canonicalTrace {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) :
    Trace L :=
  (canonicalRun (L := L) (φ := φ) (ρ := ρ)).1

def canonicalValue {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) :
    L.Carrier :=
  (canonicalRun (L := L) (φ := φ) (ρ := ρ)).2

theorem compile_correct {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) :
    L.dec (canonicalValue (L := L) (φ := φ) (ρ := ρ)) =
      Form.evalΩ (R := R) φ ρ := by
  have hvalue :
      canonicalValue (L := L) (φ := φ) (ρ := ρ) =
        Form.evalL (L := L) φ (fun i => L.enc (ρ i)) := by
    dsimp [canonicalValue, canonicalRun]
    exact run_compile_value (L := L)
      (ρ := fun i => L.enc (ρ i)) (φ := φ)
  have htransport :=
    Lens.dec_evalL (L := L) (ρ := fun i => L.enc (ρ i)) (φ := φ)
  have hdecode :
      (fun i => L.dec (L.enc (ρ i))) = ρ := by
    ext i
    simp
  simpa [canonicalValue, canonicalRun, hvalue.symm, hdecode] using htransport

end Lens

end Crypto
end HeytingLean
