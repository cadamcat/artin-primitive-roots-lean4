import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadExpansion
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.CutoffBounds
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.MajorKernelBound
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.ComparisonCounting

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII Classical
noncomputable section

/-- A raw pair sum is bounded by its absolute coefficient sum on the common-predecessor quads. -/
theorem rawPairSum_norm_le {K : ℕ} (F : PDFix K) (hF : F.Valid) (x Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (ta tb : Fin K → ℕ) (hV : ∀ i : Fin K, 0 < bandMass x (F.a i)) :
    ‖rawPairSum F x Y family beta ta tb‖ ≤
      (∏ i : Fin K, (bandMass x (F.a i))⁻¹) ^ 2 *
        (∑ q ∈ rawCommonQuads (familyTerms family x) (dyadicIntegers (family.Hn x))
          (tupleProduct ta) (tupleProduct tb), ‖coefficientQuadProduct family x beta q‖) := by
  have hν : 0 ≤ ∏ i : Fin K, (bandMass x (F.a i))⁻¹ :=
    Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (hV i).le)
  have heta := cauchyCutoff_le_one hF.2.2.2.2.1
  have hηa : ‖(F.eta ((tupleProduct ta : ℝ) / Y) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF.2.2.2.2.1.2.2.1 _)]
    exact heta _
  have hηb : ‖(F.eta ((tupleProduct tb : ℝ) / Y) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF.2.2.2.2.1.2.2.1 _)]
    exact heta _
  have hscalar : ‖(((∏ i : Fin K, (bandMass x (F.a i))⁻¹ : ℝ) : ℂ)) ^ 2‖ =
      (∏ i : Fin K, (bandMass x (F.a i))⁻¹) ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν]
  unfold rawPairSum
  rw [norm_mul, hscalar]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ ∑ q ∈ coefficientQuadChoices family x,
        ‖if ∃ h : ℕ, q.1.1 * q.1.2 - 1 = tupleProduct ta * h ∧
            q.2.1 * q.2.2 - 1 = tupleProduct tb * h then
          (F.eta ((tupleProduct ta : ℝ) / Y) : ℂ) * (F.eta ((tupleProduct tb : ℝ) / Y) : ℂ) *
            coefficientQuadProduct family x beta q else 0‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ coefficientQuadChoices family x,
        if ∃ h : ℕ, q.1.1 * q.1.2 - 1 = tupleProduct ta * h ∧
            q.2.1 * q.2.2 - 1 = tupleProduct tb * h then ‖coefficientQuadProduct family x beta q‖ else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      split_ifs
      · rw [norm_mul, norm_mul]
        have hη := mul_le_mul hηa hηb (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hη (norm_nonneg _)
      · simp only [norm_zero, le_refl]
    _ = _ := by rw [rawCommonQuads, Finset.sum_filter]; rfl

/-- A comparison pair sum is bounded by the short-determinant coefficient sum. -/
theorem comparisonPairSum_norm_le {K : ℕ} (F : PDFix K) (hF : F.Valid) (x Y R B : ℝ)
    (hY : 0 < Y) (hL : 1 ≤ Real.log x) (hB : 0 ≤ B)
    (hBound : ∀ t : ℝ, |F.psi t| ≤ B) (hSupport : ∀ t : ℝ, F.psi t ≠ 0 → |t| ≤ R)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (ta tb : Fin K → ℕ) (hV : ∀ i : Fin K, 0 < bandMass x (F.a i)) :
    ‖comparisonPairSum F x Y family beta ta tb‖ ≤
      (∏ i : Fin K, (bandMass x (F.a i))⁻¹) ^ 2 *
        (32 * B * Real.rpow (Real.log x) (3 * F.A₀) / Y) *
        (∑ q ∈ comparisonQuads (familyTerms family x) (dyadicIntegers (family.Hn x))
          (tupleProduct ta) (tupleProduct tb) Y R, ‖coefficientQuadProduct family x beta q‖) := by
  let H := 32 * B * Real.rpow (Real.log x) (3 * F.A₀) / Y
  have hPow := Real.rpow_nonneg (by linarith [hL] : 0 ≤ Real.log x) (3 * F.A₀)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hν : 0 ≤ ∏ i : Fin K, (bandMass x (F.a i))⁻¹ :=
    Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (hV i).le)
  have heta := cauchyCutoff_le_one hF.2.2.2.2.1
  have hη (t : Fin K → ℕ) : ‖(F.eta ((tupleProduct t : ℝ) / Y) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF.2.2.2.2.1.2.2.1 _)]
    exact heta _
  have hscalar : ‖(((∏ i : Fin K, (bandMass x (F.a i))⁻¹ : ℝ) : ℂ)) ^ 2‖ =
      (∏ i : Fin K, (bandMass x (F.a i))⁻¹) ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν]
  have hkernel (t : ℝ) (a b : ℕ) : ‖majorKernel x Y F.A₀ t a b F.psi‖ ≤
      if |t| ≤ R * Y then H else 0 := by
    by_cases ht : |t| ≤ R * Y
    · rw [if_pos ht]
      exact majorKernel_norm_bound x Y F.A₀ t a b F.psi B hB hBound hY hL hF.2.2.2.1
    · have hz : F.psi (t / Y) = 0 := by
        by_contra hn
        have hb := hSupport (t / Y) hn
        rw [abs_div, abs_of_pos hY] at hb
        exact ht ((div_le_iff₀ hY).mp hb)
      simp [majorKernel, hz, ht]
  unfold comparisonPairSum
  rw [norm_mul, hscalar]
  calc
    _ ≤ (∏ i : Fin K, (bandMass x (F.a i))⁻¹) ^ 2 *
        ∑ q ∈ coefficientQuadChoices family x,
          ‖(F.eta ((tupleProduct ta : ℝ) / Y) : ℂ) * (F.eta ((tupleProduct tb : ℝ) / Y) : ℂ) *
            majorKernel x Y F.A₀
              ((tupleProduct tb : ℝ) * (q.1.1 * q.1.2 : ℕ) - (tupleProduct ta : ℝ) * (q.2.1 * q.2.2 : ℕ))
              (tupleProduct ta) (tupleProduct tb) F.psi * coefficientQuadProduct family x beta q‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (sq_nonneg _)
    _ ≤ (∏ i : Fin K, (bandMass x (F.a i))⁻¹) ^ 2 *
        ∑ q ∈ coefficientQuadChoices family x,
          H * (if |(tupleProduct tb : ℝ) * (q.1.1 * q.1.2 : ℕ) -
              (tupleProduct ta : ℝ) * (q.2.1 * q.2.2 : ℕ)| ≤ R * Y then
            ‖coefficientQuadProduct family x beta q‖ else 0) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul, norm_mul, norm_mul]
      have hηab : ‖(F.eta ((tupleProduct ta : ℝ) / Y) : ℂ)‖ *
          ‖(F.eta ((tupleProduct tb : ℝ) / Y) : ℂ)‖ ≤ 1 := by
        simpa only [one_mul] using mul_le_mul (hη ta) (hη tb) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have hk := hkernel
        ((tupleProduct tb : ℝ) * (q.1.1 * q.1.2 : ℕ) - (tupleProduct ta : ℝ) * (q.2.1 * q.2.2 : ℕ)) (tupleProduct ta) (tupleProduct tb)
      have hp := mul_le_mul hηab hk (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have hp' := mul_le_mul_of_nonneg_right hp (norm_nonneg (coefficientQuadProduct family x beta q))
      split_ifs at * <;> simpa only [one_mul, zero_mul, mul_zero] using hp'
    _ = _ := by
      rw [← Finset.mul_sum, comparisonQuads, Finset.sum_filter]
      dsimp only [H, coefficientQuadChoices]
      ring

end
end ArtinPrimitiveRoots.TypeII.PD
