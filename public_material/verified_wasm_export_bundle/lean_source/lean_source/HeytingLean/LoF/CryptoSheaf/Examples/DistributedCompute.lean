import HeytingLean.LoF.CryptoSheaf.HomomorphicMorphism

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Examples

open HeytingLean.LoF

variable {α : Type u} [PrimaryAlgebra α]

/-- Canonical homomorphic evaluation agrees with `R ∘ f` on encryptions (meet-right). -/
theorem decrypt_eval_encrypt_inf_right
    (R : Reentry α) (y : α) (a : α) :
    (((HomomorphicScheme.canonical R).eval (fun x => x ⊓ y)
        (liftable_inf_right (R := R) y)
        ((HomomorphicScheme.canonical R).encrypt a)) : α)
      = R (a ⊓ y) := by
  simpa using
    (HomomorphicScheme.canonical R).correct (fun x => x ⊓ y)
      (liftable_inf_right (R := R) y) a

/-- Right-implication operator on Ωᴿ applied to an encrypted input. -/
theorem himpRight_encrypt_coe_eq (R : Reentry α) (a : α) (b : R.Omega) :
    ((himpRight (R := R) b ((HomomorphicScheme.canonical R).encrypt a)) : α)
      = (R a) ⇨ (b : α) :=
  himpRight_encrypt_coe (R := R) a b

/-- Canonical homomorphic evaluation agrees with `R ∘ (· ⊔ y)` on encryptions (sup-left). -/
theorem decrypt_eval_encrypt_sup_left
    (R : Reentry α) (y : α) (a : α) :
    (((HomomorphicScheme.canonical R).eval (fun x => x ⊔ y)
        (liftable_sup_left (R := R))
        ((HomomorphicScheme.canonical R).encrypt a)) : α)
      = R (a ⊔ y) := by
  simpa using
    (HomomorphicScheme.canonical R).correct (fun x => x ⊔ y)
      (liftable_sup_left (R := R)) a

/-- Canonical homomorphic evaluation agrees with `R ∘ (y ⊔ ·)` on encryptions (sup-right). -/
theorem decrypt_eval_encrypt_sup_right
    (R : Reentry α) (y : α) (a : α) :
    (((HomomorphicScheme.canonical R).eval (fun x => y ⊔ x)
        (liftable_sup_right (R := R))
        ((HomomorphicScheme.canonical R).encrypt a)) : α)
      = R (y ⊔ a) := by
  simpa using
    (HomomorphicScheme.canonical R).correct (fun x => y ⊔ x)
      (liftable_sup_right (R := R)) a

end Examples
end CryptoSheaf
end LoF
end HeytingLean
