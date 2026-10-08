import ArtinPrimitiveRoots.Ext.TypeIIInputs

namespace ArtinPrimitiveRoots.Proofs.c_typeii_sol

open Classical MeasureTheory Filter
open scoped FourierTransform

private theorem norm_complex_log_phase (v t : ℝ) :
    ‖Complex.exp (Complex.I * (v : ℂ) * (t : ℂ))‖ = 1 := by
  have he : Complex.I * (v : ℂ) * (t : ℂ) = Complex.I * ((v * t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal]

private theorem logFourierTransform_continuous (Ψ : ℝ → ℝ)
    (hΨ : Continuous Ψ) (hsupp : Function.support Ψ ⊆ Set.Ioo 1 2) :
    Continuous (ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ) := by
  let g : ℝ → ℂ := fun s => (Ψ (Real.exp s) : ℂ)
  have hgcont : Continuous g := by
    dsimp [g]
    fun_prop
  have hgsupp : Function.support g ⊆ Set.Icc (0 : ℝ) 1 := by
    apply Function.support_subset_iff'.2
    intro s hs
    dsimp [g]
    by_contra hne
    have hne' : Ψ (Real.exp s) ≠ 0 := by
      intro hzero
      apply hne
      exact_mod_cast hzero
    have hm : Real.exp s ∈ Function.support Ψ := hne'
    have hband := hsupp hm
    have hs' : s < 0 ∨ 1 < s := by
      by_cases h0 : 0 ≤ s
      · right
        exact lt_of_not_ge (fun h1 => hs ⟨h0, h1⟩)
      · left
        exact lt_of_not_ge h0
    rcases hs' with hslo | hshi
    · have hexp : Real.exp s < 1 := Real.exp_lt_one_iff.mpr hslo
      linarith [hband.1]
    · have hexp : 2 < Real.exp s := by
        calc
          2 < Real.exp 1 := Real.exp_one_gt_two
          _ < Real.exp s := Real.exp_lt_exp.mpr hshi
      linarith [hband.2]
  have hgint : Integrable g :=
    hgcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hgsupp)
  have hFcont : Continuous (fun t : ℝ => 𝓕 g t) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume
      (innerₗ ℝ) g)
    have hL : Continuous (fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2) := by fun_prop
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      hL hgint
  have hrepr : ∀ v : ℝ,
      ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * 𝓕 g (v / (2 * Real.pi)) := by
    intro v
    rw [ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform,
      Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul, Complex.ofReal_div]
    congr 1
    apply integral_congr_ae
    filter_upwards with s
    have he : (↑(-2 * Real.pi * s * (v / (2 * Real.pi))) : ℂ) * Complex.I =
        -Complex.I * v * s := by
      push_cast
      field_simp
    rw [he]
    simp [g, mul_comm]
  have hfun :
      ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ =
        fun v => ((1 / (2 * Real.pi) : ℝ) : ℂ) * 𝓕 g (v / (2 * Real.pi)) := by
    funext v
    exact hrepr v
  rw [hfun]
  exact continuous_const.mul (hFcont.comp (by fun_prop))

/-- A logarithmic saving on the central frequency range and a fixed global bound suffice
for an integrated saving, by rapid decay of the logarithmic Fourier transform. -/
theorem log_fourier_bilinear_bound (Ψ : ℝ → ℝ)
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hsupp : Function.support Ψ ⊆ Set.Ioo 1 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ x A B : ℝ,
      0 ≤ A → 0 ≤ B → ∀ S : ℝ → ℂ, Continuous S →
        (∀ v : ℝ, ‖S v‖ ≤ B) →
        (∀ v : ℝ, |v| ≤ L → ‖S v‖ ≤ A * Real.rpow L (-6 : ℝ)) →
        ‖∫ v : ℝ, ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v *
          Complex.exp (-Complex.I * v * Real.log x) * S v‖ ≤
            C * (A + B) * Real.rpow L (-6 : ℝ) := by
  obtain ⟨hInv, hDecay⟩ := ArtinPrimitiveRoots.Ext.TypeIIInputs.fourier_inversion
    Ψ hsmooth hsupp
  obtain ⟨C₂, hC₂, hDecay₂⟩ := hDecay 2
  obtain ⟨C₈, hC₈, hDecay₈⟩ := hDecay 8
  have hFTcont := logFourierTransform_continuous Ψ hsmooth.continuous hsupp
  have hmajorant : Integrable (fun v : ℝ => (1 + |v|) ^ (-2 : ℝ)) := by
    simpa [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (by norm_num :
        (Module.finrank ℝ ℝ : ℝ) < 2))
  have hFTnormInt : Integrable
      (fun v : ℝ => ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖) := by
    refine (hmajorant.const_mul C₂).mono' hFTcont.norm.aestronglyMeasurable ?_
    filter_upwards [] with v
    simpa [Real.norm_eq_abs, mul_comm] using hDecay₂ v
  let J : ℝ := ∫ v : ℝ, (1 + |v|) ^ (-2 : ℝ)
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun v => by positivity
  have hFTnormBound :
      (∫ v : ℝ, ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖) ≤
        C₂ * J := by
    calc
      _ ≤ ∫ v : ℝ, C₂ * (1 + |v|) ^ (-2 : ℝ) := by
        apply integral_mono hFTnormInt (hmajorant.const_mul C₂)
        intro v
        simpa [Real.norm_eq_abs, mul_comm] using hDecay₂ v
      _ = C₂ * J := by simp [J, integral_const_mul]
  refine ⟨(C₂ + C₈) * J + 1, by positivity, ?_⟩
  intro L hL x A B hA hB S hS hGlobal hNear
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hPow : 0 ≤ Real.rpow L (-6 : ℝ) := (Real.rpow_pos_of_pos hLpos _).le
  let Core : Set ℝ := Set.Icc (-L) L
  have hCoreMeas : MeasurableSet Core := isClosed_Icc.measurableSet
  let P : ℝ → ℂ := fun v =>
    ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v *
      Complex.exp (-Complex.I * v * Real.log x) * S v
  have hPhaseNorm (v : ℝ) : ‖Complex.exp (-Complex.I * v * Real.log x)‖ = 1 := by
    have he : -Complex.I * v * Real.log x =
        Complex.I * ((-v : ℝ) : ℂ) * Real.log x := by push_cast; ring
    rw [he]
    exact norm_complex_log_phase (-v) (Real.log x)
  have hPcont : Continuous P := by
    exact (hFTcont.mul (by fun_prop)).mul hS
  have hPnorm (v : ℝ) : ‖P v‖ =
      ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖ * ‖S v‖ := by
    simp only [P, norm_mul, hPhaseNorm, mul_one]
  have hPpoint (v : ℝ) : ‖P v‖ ≤
      B * ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖ := by
    rw [hPnorm]
    calc
      _ ≤ ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖ * B :=
        mul_le_mul_of_nonneg_left (hGlobal v) (norm_nonneg _)
      _ = _ := by ring
  have hPint : Integrable P := by
    refine (hFTnormInt.const_mul B).mono' hPcont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hPpoint
  let Acore : ℝ := A * Real.rpow L (-6 : ℝ)
  have hAcore : 0 ≤ Acore := mul_nonneg hA hPow
  have hCorePoint (v : ℝ) : Core.indicator (fun v => ‖P v‖) v ≤
      Acore * ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖ := by
    by_cases hv : v ∈ Core
    · simp only [Set.indicator_of_mem hv]
      have hvabs : |v| ≤ L := abs_le.mpr hv
      rw [hPnorm]
      calc
        _ ≤ ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖ * Acore :=
          mul_le_mul_of_nonneg_left (hNear v hvabs) (norm_nonneg _)
        _ = _ := by ring
    · simp only [Set.indicator_of_notMem hv]
      exact mul_nonneg hAcore (norm_nonneg _)
  have hCoreInt : (∫ v : ℝ, Core.indicator (fun v => ‖P v‖) v) ≤ Acore * C₂ * J := by
    calc
      _ ≤ ∫ v : ℝ, Acore *
          ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖ := by
        apply integral_mono (hPint.norm.indicator hCoreMeas) (hFTnormInt.const_mul Acore)
        intro v
        exact hCorePoint v
      _ = Acore * (∫ v : ℝ,
          ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖) :=
        integral_const_mul _ _
      _ ≤ Acore * (C₂ * J) := mul_le_mul_of_nonneg_left hFTnormBound hAcore
      _ = Acore * C₂ * J := by ring
  have hCoreNorm : ‖∫ v : ℝ in Core, P v‖ ≤ Acore * C₂ * J := by
    calc
      _ ≤ ∫ v : ℝ in Core, ‖P v‖ := norm_integral_le_integral_norm _
      _ = ∫ v : ℝ, Core.indicator (fun v => ‖P v‖) v :=
        (integral_indicator hCoreMeas).symm
      _ ≤ Acore * C₂ * J := hCoreInt
  have hTailFTPoint (v : ℝ) : Coreᶜ.indicator (fun v =>
      ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖) v ≤
        C₈ * Real.rpow L (-6 : ℝ) * (1 + |v|) ^ (-2 : ℝ) := by
    by_cases hv : v ∈ Coreᶜ
    · simp only [Set.indicator_of_mem hv]
      have hvnot : ¬ (-L ≤ v ∧ v ≤ L) := by
        simpa only [Core, Set.mem_compl_iff, Set.mem_Icc] using hv
      have hvabs : L ≤ |v| := by
        by_contra hnot
        exact hvnot (abs_le.mp (le_of_lt (lt_of_not_ge hnot)))
      let Q : ℝ := 1 + |v|
      have hQ : 0 < Q := by dsimp [Q]; positivity
      have hLQ : L ≤ Q := by dsimp [Q]; linarith
      have hsplit : Real.rpow Q (-8 : ℝ) =
          Real.rpow Q (-6 : ℝ) * Real.rpow Q (-2 : ℝ) := by
        change Q ^ (-8 : ℝ) = Q ^ (-6 : ℝ) * Q ^ (-2 : ℝ)
        rw [show (-8 : ℝ) = (-6) + (-2) by norm_num, Real.rpow_add hQ]
      have hmono : Real.rpow Q (-6 : ℝ) ≤ Real.rpow L (-6 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hLpos hLQ (by norm_num)
      calc
        _ ≤ C₈ * Real.rpow Q (-8 : ℝ) := hDecay₈ v
        _ = C₈ * (Real.rpow Q (-6 : ℝ) * Real.rpow Q (-2 : ℝ)) := by rw [hsplit]
        _ ≤ C₈ * (Real.rpow L (-6 : ℝ) * Real.rpow Q (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hmono (Real.rpow_pos_of_pos hQ _).le) hC₈.le
        _ = _ := by dsimp [Q]; ring
    · simp only [Set.indicator_of_notMem hv]
      exact mul_nonneg (mul_nonneg hC₈.le hPow)
        (Real.rpow_pos_of_pos (by positivity : 0 < 1 + |v|) (-2 : ℝ)).le
  have hTailFT : (∫ v : ℝ in Coreᶜ,
      ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖) ≤
        C₈ * Real.rpow L (-6 : ℝ) * J := by
    calc
      _ = ∫ v : ℝ, Coreᶜ.indicator (fun v =>
          ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖) v :=
        (integral_indicator hCoreMeas.compl).symm
      _ ≤ ∫ v : ℝ, (C₈ * Real.rpow L (-6 : ℝ)) * (1 + |v|) ^ (-2 : ℝ) := by
        apply integral_mono (hFTnormInt.indicator hCoreMeas.compl)
          (hmajorant.const_mul (C₈ * Real.rpow L (-6 : ℝ)))
        intro v
        exact hTailFTPoint v
      _ = C₈ * Real.rpow L (-6 : ℝ) * J := integral_const_mul _ _
  have hTailPPoint (v : ℝ) : Coreᶜ.indicator (fun v => ‖P v‖) v ≤
      B * Coreᶜ.indicator (fun v =>
        ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖) v := by
    by_cases hv : v ∈ Coreᶜ
    · simp only [Set.indicator_of_mem hv]
      exact hPpoint v
    · simp only [Set.indicator_of_notMem hv, mul_zero, le_refl]
  have hTailPInt : (∫ v : ℝ, Coreᶜ.indicator (fun v => ‖P v‖) v) ≤
      B * C₈ * Real.rpow L (-6 : ℝ) * J := by
    calc
      _ ≤ ∫ v : ℝ, B * Coreᶜ.indicator (fun v =>
          ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖) v := by
        apply integral_mono (hPint.norm.indicator hCoreMeas.compl)
          ((hFTnormInt.indicator hCoreMeas.compl).const_mul B)
        intro v
        exact hTailPPoint v
      _ = B * (∫ v : ℝ in Coreᶜ,
          ‖ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v‖) := by
        rw [integral_const_mul, integral_indicator hCoreMeas.compl]
      _ ≤ B * (C₈ * Real.rpow L (-6 : ℝ) * J) :=
        mul_le_mul_of_nonneg_left hTailFT hB
      _ = _ := by ring
  have hTailNorm : ‖∫ v : ℝ in Coreᶜ, P v‖ ≤
      B * C₈ * Real.rpow L (-6 : ℝ) * J := by
    calc
      _ ≤ ∫ v : ℝ in Coreᶜ, ‖P v‖ := norm_integral_le_integral_norm _
      _ = ∫ v : ℝ, Coreᶜ.indicator (fun v => ‖P v‖) v :=
        (integral_indicator hCoreMeas.compl).symm
      _ ≤ _ := hTailPInt
  calc
    ‖∫ v : ℝ, ArtinPrimitiveRoots.Ext.TypeIIInputs.logFourierTransform Ψ v *
        Complex.exp (-Complex.I * v * Real.log x) * S v‖ = ‖∫ v : ℝ, P v‖ := rfl
    _ ≤ ‖∫ v : ℝ in Core, P v‖ + ‖∫ v : ℝ in Coreᶜ, P v‖ := by
      rw [← integral_add_compl hCoreMeas hPint]
      exact norm_add_le _ _
    _ ≤ Acore * C₂ * J + B * C₈ * Real.rpow L (-6 : ℝ) * J :=
      add_le_add hCoreNorm hTailNorm
    _ = (A * C₂ + B * C₈) * J * Real.rpow L (-6 : ℝ) := by
      dsimp [Acore]
      ring
    _ ≤ ((A + B) * (C₂ + C₈)) * J * Real.rpow L (-6 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hPow
      apply mul_le_mul_of_nonneg_right _ hJ
      nlinarith [mul_nonneg hA hC₈.le, mul_nonneg hB hC₂.le]
    _ = ((C₂ + C₈) * J) * (A + B) * Real.rpow L (-6 : ℝ) := by ring
    _ ≤ ((C₂ + C₈) * J + 1) * (A + B) * Real.rpow L (-6 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hPow
      exact mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hA hB)

end ArtinPrimitiveRoots.Proofs.c_typeii_sol
