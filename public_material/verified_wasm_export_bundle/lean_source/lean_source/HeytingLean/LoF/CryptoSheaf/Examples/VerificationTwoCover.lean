import HeytingLean.LoF.CryptoSheaf.Site
import HeytingLean.LoF.CryptoSheaf.Presheaf
import HeytingLean.LoF.CryptoSheaf.Verification

/-
CryptoSheaf/Examples/VerificationTwoCover

Specializes `local_top_global_top` to a tiny two-element poset site (`Bool`),
with a trivial computation sheaf and a 2-element cover of `U = true`.
-/

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Examples

open HeytingLean.LoF

namespace VerificationTwoCover

def boolSite : PosetSite Bool where
  Logic := fun _ => Prop
  heytingInst := fun _ => inferInstance
  restrict := by intro U V h; exact id
  restrictHom := by intro U V h; exact HeytingHom.id _
  restrictHom_toFun := by intro U V h; rfl
  restrict_id := by intro U x; rfl
  restrict_comp := by intro U V W hVU hWV x; rfl

def trivialPresheaf : CompPresheaf boolSite where
  Sections := fun _ => Unit
  value := fun _ _ => True
  restrict := by intro U V h s; exact s
  restrict_id := by intro U s; cases s; rfl
  restrict_comp := by intro U V W hVU hWV s; cases s; rfl
  value_restrict := by intro U V h s; cases s; rfl

def trivialSheaf : CompSheaf boolSite :=
  { toCompPresheaf := trivialPresheaf,
    sheaf :=
      { glue := by intro U cover cover_le fam; exact (),
        glue_restrict := by intro U cover cover_le fam V hV; rfl,
        glue_unique := by intro U cover cover_le fam s hs; cases s; rfl } }

/-- A concrete 2-cover verification: locals have value `⊤` so the glued value is `⊤`. -/
theorem twoCover_glue_top :
    let U := true
    let cover := [true, false]
    let cover_le : ∀ V ∈ cover, V ≤ U := by intro V h; cases V <;> decide
    let fam : CompatibleFamily boolSite trivialPresheaf U cover cover_le :=
      { local_sections := fun _ _ => (),
        compatible := by intro _ _ _ _ _ _ _; rfl }
    trivialPresheaf.value U (trivialSheaf.sheaf.glue U cover cover_le fam) = True := by
  intro U cover cover_le fam
  -- `local_top_global_top` with `U ∈ cover` and locals = ⊤.
  have hU : U ∈ cover := by simp [U, cover]
  have := local_top_global_top (S := boolSite) (F := trivialSheaf)
    (U := U) (cover := cover) (cover_le := cover_le) (fam := fam)
    (hU := hU) (local_tops := by intro V hV; rfl)
  simpa using this

end VerificationTwoCover

end Examples
end CryptoSheaf
end LoF
end HeytingLean
