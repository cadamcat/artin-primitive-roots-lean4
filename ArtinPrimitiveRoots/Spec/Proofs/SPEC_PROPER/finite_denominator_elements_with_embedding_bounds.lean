import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.finite_integral_elements_with_embedding_bounds

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- A common positive integral denominator and bounded embeddings give a finite field set.
Denominator step. Uses
finite_integral_elements_with_embedding_bounds; feeds siegel_high_height_overlap_finite. -/
theorem finite_denominator_elements_with_embedding_bounds (D : ℕ) (hD : 0 < D)
    (R : ℝ) (hR : 0 ≤ R) :
    {μ : F | HasDenominatorBound F D μ ∧
      ∀ w : InfinitePlace F, ‖w.embedding μ‖ ≤ R}.Finite := by
  classical
  let T : Set (𝓞 F) := {b | ∀ w : InfinitePlace F,
    ‖w.embedding (algebraMap (𝓞 F) F b)‖ ≤ (D : ℝ) * R}
  have hT : T.Finite :=
    finite_integral_elements_with_embedding_bounds ((D : ℝ) * R)
      (mul_nonneg (Nat.cast_nonneg D) hR)
  let g : 𝓞 F → F := fun b => (D : F)⁻¹ * (b : F)
  have himage : (g '' T).Finite := hT.image g
  apply himage.subset
  intro μ hμ
  rcases hμ.1 with ⟨b, hb⟩
  have hD0 : (D : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hb' : (D : F) * μ = (b : F) := by simpa using hb
  have hbound : b ∈ T := by
    intro w
    have heq : w.embedding (algebraMap (𝓞 F) F b) =
        (D : ℂ) * w.embedding μ := by
      rw [← hb]
      simp
    have hnorm : ‖w.embedding (algebraMap (𝓞 F) F b)‖ =
        (D : ℝ) * ‖w.embedding μ‖ := by
      rw [heq, norm_mul]
      simp
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (hμ.2 w) (Nat.cast_nonneg D)
  refine ⟨b, hbound, ?_⟩
  dsimp [g]
  calc
    (D : F)⁻¹ * (b : F) = (D : F)⁻¹ * ((D : F) * μ) := by rw [← hb']
    _ = μ := by field_simp [hD0]
end ArtinPrimitiveRoots.A1.Spec
