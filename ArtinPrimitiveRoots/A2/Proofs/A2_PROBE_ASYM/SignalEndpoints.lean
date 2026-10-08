import ArtinPrimitiveRoots.A2.FSide

set_option autoImplicit false

open MeasureTheory Complex
open scoped Classical

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_pasym_sol
open ArtinPrimitiveRoots.A2

/-- Moving the Gaussian contour to the right gives every positive power at zero. -/
theorem fEta_small_bounds_of_bounds (H L : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 998 / 1000 < s.re})
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hHb : ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖H s‖ ≤ B)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B) :
    ∀ A0 : ℝ, 0 < A0 → ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ,
      0 < Z → Z ≤ 1 → ‖fEta H L Z‖ ≤ C * Z ^ A0 := by
  intro A0 hA0
  obtain ⟨BH, hBHbound⟩ := hHb
  obtain ⟨BL, hBLbound⟩ := hLb
  have hBH : 0 ≤ BH := (norm_nonneg (H 2)).trans (hBHbound 2 (by norm_num))
  have hBL : 0 ≤ BL := (norm_nonneg ((L 2)⁻¹)).trans (hBLbound 2 (by norm_num))
  let B : ℝ := max 2 (A0 + 8 / 15)
  have hB : 2 ≤ B := le_max_left _ _
  have hBA0 : A0 ≤ B - 8 / 15 := by
    have hh : A0 + 8 / 15 ≤ B := le_max_right _ _
    linarith
  let G : ℂ → ℂ := fun s => H s * (L s)⁻¹
  have hGdiff : DifferentiableOn ℂ G {s : ℂ | 1 < s.re} :=
    (hH.mono (by intro s hs; change 1 < s.re at hs; change 998 / 1000 < s.re; linarith)).mul
      (hL.inv hL0)
  have hGbound (s : ℂ) (hs : 2 ≤ s.re) : ‖G s‖ ≤ BH * BL := by
    dsimp [G]
    rw [norm_mul]
    exact mul_le_mul (hBHbound s (by linarith)) (hBLbound s hs)
      (norm_nonneg _) hBH
  let C : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖ * Real.exp ((B - 5 / 6) ^ 2) *
    (BH * BL) * ∫ t : ℝ, Real.exp (-(t ^ 2))
  have hC : 0 ≤ C := by
    have hg : 0 ≤ ∫ t : ℝ, Real.exp (-(t ^ 2)) :=
      integral_nonneg (fun t => (Real.exp_pos _).le)
    dsimp [C]
    positivity
  refine ⟨C + 1, by linarith, ?_⟩
  intro Z hZ hZ1
  let F : ℂ → ℂ := OAI.SevenEighths.Continuation.gaussianContourIntegrand
    G (-(8 / 15 : ℝ)) Z
  have hFdiff : DifferentiableOn ℂ F {s : ℂ | 2 ≤ s.re ∧ s.re ≤ B} := by
    apply OAI.SevenEighths.Continuation.gaussianContourIntegrand_differentiableOn
      (hGdiff.mono (by intro s hs; exact lt_of_lt_of_le (by norm_num) hs.1)) _ hZ
  have hFbound : ∀ x ∈ Set.Icc (2 : ℝ) B, ∀ t : ℝ, ‖F ((x : ℂ) + t * I)‖ ≤
      (Z ^ ((2 : ℝ) - 8 / 15) * Real.exp ((B - 5 / 6) ^ 2) * (BH * BL)) *
        Real.exp (-(t ^ 2)) := by
    intro x hx t
    dsimp [F]
    rw [OAI.SevenEighths.Continuation.norm_gaussianContourIntegrand _ _ _ _ hZ]
    have hpow : Z ^ (x - 8 / 15 : ℝ) ≤ Z ^ ((2 : ℝ) - 8 / 15) :=
      Real.rpow_le_rpow_of_exponent_ge hZ hZ1 (by linarith [hx.1])
    have hexp : Real.exp ((x - 5 / 6) ^ 2) ≤ Real.exp ((B - 5 / 6) ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hx.1, hx.2]
    have hquot := hGbound ((x : ℂ) + t * I) (by simpa using hx.1)
    have hprod := mul_le_mul
      (mul_le_mul hpow hexp (by positivity) (by positivity)) hquot
      (norm_nonneg _) (by positivity)
    simpa only [sub_eq_add_neg, mul_assoc] using
      mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-(t ^ 2))).le
  have hshift := OAI.SevenEighths.Continuation.vertical_integral_eq_of_gaussian_bound
    F hB hFdiff hFbound
  have hshift' : (∫ t : ℝ, F ((2 : ℂ) + t * I)) =
      ∫ t : ℝ, F ((B : ℂ) + t * I) := by
    simpa only [Complex.ofReal_ofNat] using hshift
  have hlinebound (t : ℝ) : ‖F ((B : ℂ) + t * I)‖ ≤
      (Z ^ (B - 8 / 15) * Real.exp ((B - 5 / 6) ^ 2) * (BH * BL)) *
        Real.exp (-(t ^ 2)) := by
    dsimp [F]
    rw [OAI.SevenEighths.Continuation.norm_gaussianContourIntegrand _ _ _ _ hZ]
    have hquot := hGbound ((B : ℂ) + t * I) (by simpa using hB)
    have hprod := mul_le_mul_of_nonneg_left hquot
      (mul_nonneg (Real.rpow_nonneg hZ.le (B - 8 / 15))
        (Real.exp_pos ((B - 5 / 6) ^ 2)).le)
    simpa only [sub_eq_add_neg, mul_assoc] using
      mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-(t ^ 2))).le
  have hgauss : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hint := norm_integral_le_of_norm_le
    (hgauss.const_mul (Z ^ (B - 8 / 15) * Real.exp ((B - 5 / 6) ^ 2) * (BH * BL)))
    (f := fun t : ℝ => F ((B : ℂ) + t * I)) (ae_of_all _ hlinebound)
  have hnew : ‖(1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F ((B : ℂ) + t * I)‖ ≤
      C * Z ^ (B - 8 / 15) := by
    have hh := mul_le_mul_of_nonneg_left hint (norm_nonneg (1 / (2 * Real.pi) : ℂ))
    rw [integral_const_mul] at hh
    simpa [C, norm_mul, mul_assoc, mul_left_comm, mul_comm] using hh
  have hCstar (s : ℂ) : Cstar s = s + ((-(8 / 15) : ℝ) : ℂ) := by
    simp only [Cstar, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hsignal : fEta H L Z =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F ((2 : ℂ) + t * I) := by
    unfold fEta
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    rw [hCstar]
    simp only [F, OAI.SevenEighths.Continuation.gaussianContourIntegrand,
      G, amplitude, div_eq_mul_inv]
    ring
  have hpower : Z ^ (B - 8 / 15) ≤ Z ^ A0 :=
    Real.rpow_le_rpow_of_exponent_ge hZ hZ1 hBA0
  calc
    ‖fEta H L Z‖ = ‖(1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, F ((B : ℂ) + t * I)‖ := by rw [hsignal, hshift']
    _ ≤ C * Z ^ (B - 8 / 15) := hnew
    _ ≤ C * Z ^ A0 := mul_le_mul_of_nonneg_left hpower hC
    _ ≤ (C + 1) * Z ^ A0 :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _)

end ArtinPrimitiveRoots.Proofs.a2_pasym_sol
