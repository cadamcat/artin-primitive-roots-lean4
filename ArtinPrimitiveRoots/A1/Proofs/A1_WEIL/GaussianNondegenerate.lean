import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianFourierSeparation

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

local instance nondegenerateMeasurable (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance nondegenerateBorel (v : FinPlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- A trivial multiplicative defect of the actual Gaussian index forces a square.
Cancel the explicit normalization to compare stable Gaussians by a nonzero scalar.
The checked Fourier support separation rules out that comparison for a nonsquare.
Character regularity and the Haar Jacobian remain explicit. -/
theorem local_index_defect_nondegenerate (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F)
    (hregular : LocalCharacterRegular A v)
    (hscale : ∀ c : (v.adicCompletion F)ˣ,
      Measure.map (fun x : v.adicCompletion F => (c : v.adicCompletion F) * x) (W.measure v) =
        (ENNReal.ofReal ‖(c : v.adicCompletion F)‖)⁻¹ • W.measure v)
    (a : (v.adicCompletion F)ˣ)
    (hmul : ∀ b, W.index v a * W.index v b = W.index v (a * b)) :
    ∃ c : (v.adicCompletion F)ˣ, a = c ^ 2 := by
  classical
  by_cases ha : ∃ c : (v.adicCompletion F)ˣ, a = c ^ 2
  · exact ha
  · exfalso
    have haK : ¬ IsSquare (a : v.adicCompletion F) := by
      rintro ⟨c, hc⟩
      have hc0 : c ≠ 0 := by
        intro hc0
        apply a.ne_zero
        simpa only [hc0, mul_zero] using hc
      apply ha
      refine ⟨Units.mk0 c hc0, ?_⟩
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, pow_two, Units.val_mul, Units.val_mk0] using hc
    have hnorm : ∀ x : v.adicCompletion F, absFin v x = ‖x‖ := by
      intro x
      rw [absFin, dite_eq_left (NumberField.HeightOneSpectrum.absNorm_ne_zero v),
        NumberField.FinitePlace.norm_def]
    let I := fun c : (v.adicCompletion F)ˣ => W.stableValue v c
    let R := fun c : (v.adicCompletion F)ˣ =>
      ((‖(c : v.adicCompletion F)‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ)
    have hIne : ∀ c, I c ≠ 0 := fun c => W.integral_ne_zero v c
    have hRne : ∀ c, R c ≠ 0 := by
      intro c
      dsimp only [R]
      exact_mod_cast (Real.rpow_pos_of_pos (norm_pos_iff.mpr c.ne_zero) (1 / 2 : ℝ)).ne'
    have hRmul : ∀ b, R (a * b) = R a * R b := by
      intro b
      dsimp only [R]
      rw [Units.val_mul, norm_mul,
        Real.mul_rpow (norm_nonneg (a : v.adicCompletion F)) (norm_nonneg (b : v.adicCompletion F)),
        Complex.ofReal_mul]
    have hindex : ∀ c, (W.index v c : ℂ) = R c * I c / I 1 := by
      intro c
      change ((absFin v (c : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        I c / I 1 = R c * I c / I 1
      rw [hnorm]
    let C := I a / I 1
    have hCne : C ≠ 0 := div_ne_zero (hIne a) (hIne 1)
    have hIrelation : ∀ b, I (a * b) = C * I b := by
      intro b
      have hval := congrArg (fun z : ℂˣ => (z : ℂ)) (hmul b)
      simp only [Units.val_mul, hindex, hRmul] at hval
      have hIeq : I a * I b = I (a * b) * I 1 := by
        apply mul_left_cancel₀ (mul_ne_zero (hRne a) (hRne b))
        field_simp [hIne 1] at hval
        linear_combination hval
      calc
        I (a * b) = (I (a * b) * I 1) / I 1 := by
          rw [mul_div_cancel_right₀ _ (hIne 1)]
        _ = (I a * I b) / I 1 := by rw [← hIeq]
        _ = C * I b := by dsimp only [C]; ring
    have hfreq : ∀ t : v.adicCompletion F,
        frequencyStableValue W v a t = C * frequencyStableValue W v 1 t := by
      intro t
      by_cases ht : t = 0
      · simp only [frequencyStableValue, dite_eq_left ht, mul_zero]
      · simp only [frequencyStableValue, dite_eq_right ht, one_mul]
        exact hIrelation (Units.mk0 t ht)
    obtain ⟨M, hzero, hnonzero⟩ :=
      stable_gaussian_fourier_separation A W v hregular hscale a haK
    have hint : (∫ t in localBallInt v M,
        A.ψ v (-t) * frequencyStableValue W v a t ∂W.measure v) =
        C * (∫ t in localBallInt v M,
          A.ψ v (-t) * frequencyStableValue W v 1 t ∂W.measure v) := by
      calc
        (∫ t in localBallInt v M, A.ψ v (-t) * frequencyStableValue W v a t ∂W.measure v) =
            ∫ t in localBallInt v M,
              C * (A.ψ v (-t) * frequencyStableValue W v 1 t) ∂W.measure v := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t => by
            change A.ψ v (-t) * frequencyStableValue W v a t =
              C * (A.ψ v (-t) * frequencyStableValue W v 1 t)
            rw [hfreq t]
            ring
        _ = _ := integral_const_mul C _
    rw [hzero] at hint
    exact (mul_ne_zero hCne hnonzero) hint.symm

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
