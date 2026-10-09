import Mathlib

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical MeasureTheory

noncomputable section

/-- A Fourier cutoff is bounded by its inner density mass and its outer tail mass. -/
theorem cutoff_integral_norm_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [CompleteSpace E]
    (w : ℝ → ℂ) (V : ℝ → E) (T : Set ℝ) (hT : MeasurableSet T)
    (hw : Integrable (fun u : ℝ => ‖w u‖)) (a b C : ℝ)
    (hinner : ∀ u ∈ T, ‖V u‖ ≤ a*C)
    (houter : ∀ u ∉ T, ‖V u‖ ≤ b*C) :
    ‖∫ u : ℝ, w u • V u‖ ≤
    ((∫ u : ℝ in T, ‖w u‖)*a + (∫ u : ℝ in Tᶜ, ‖w u‖)*b)*C := by
  let g₁ : ℝ → ℝ := T.indicator (fun u => ‖w u‖*(a*C))
  let g₂ : ℝ → ℝ := Tᶜ.indicator (fun u => ‖w u‖*(b*C))
  have hg₁ : Integrable g₁ := (hw.mul_const (a*C)).integrableOn.integrable_indicator hT
  have hg₂ : Integrable g₂ := (hw.mul_const (b*C)).integrableOn.integrable_indicator hT.compl
  have hpoint (u : ℝ) : ‖w u • V u‖ ≤ g₁ u + g₂ u := by
    rw [norm_smul]
    by_cases hu : u ∈ T
    · simpa [g₁, g₂, hu] using
        mul_le_mul_of_nonneg_left (hinner u hu) (norm_nonneg (w u))
    · simpa [g₁, g₂, hu] using
        mul_le_mul_of_nonneg_left (houter u hu) (norm_nonneg (w u))
  calc
    _ ≤ ∫ u : ℝ, g₁ u + g₂ u :=
      norm_integral_le_of_norm_le (hg₁.add hg₂) (Filter.Eventually.of_forall hpoint)
    _ = (∫ u : ℝ in T, ‖w u‖)*(a*C) + (∫ u : ℝ in Tᶜ, ‖w u‖)*(b*C) := by
      rw [integral_add hg₁ hg₂]
      dsimp only [g₁, g₂]
      rw [integral_indicator hT, integral_indicator hT.compl,
        integral_mul_const, integral_mul_const]
    _ = _ := by ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
