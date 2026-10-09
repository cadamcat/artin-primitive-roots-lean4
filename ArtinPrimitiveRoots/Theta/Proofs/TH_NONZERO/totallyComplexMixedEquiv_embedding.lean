import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

set_option autoImplicit false
open NumberField
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F]

/-- Identify the mixed archimedean space of a totally complex field with
the complex coordinate at every infinite place. -/
def totallyComplexMixedEquiv :
    NumberField.mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace F → ℂ) where
  toFun x w := x.2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun x := (fun _ => 0, fun w => x w.val)
  left_inv x := by
    apply Prod.ext
    · funext w
      exact False.elim ((InfinitePlace.not_isReal_iff_isComplex.mpr
        (IsTotallyComplex.isComplex w.val)) w.property)
    · funext w
      rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The mixed-space equivalence sends the mixed embedding to the
coordinatewise embeddings used by the theta torus. -/
theorem totallyComplexMixedEquiv_embedding (x : F) :
    totallyComplexMixedEquiv F (NumberField.mixedEmbedding F x) =
      (fun w : InfinitePlace F => w.embedding x) := by
  funext w
  exact NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex F x
    ⟨w, IsTotallyComplex.isComplex w⟩

end ArtinPrimitiveRoots.A1.Theta
