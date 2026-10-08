import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

/-- Nonnegative summands in a dyadic partition are bounded by its total mass. -/
theorem cauchyCutoff_le_one {eta : ℝ → ℝ} (heta : IsCauchyCutoff eta) (y : ℝ) :
    eta y ≤ 1 := by
  by_cases hzero : eta y = 0
  · simp [hzero]
  have hy : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (heta.2.1 (by exact hzero)).1
  have hpart := heta.2.2.2 y hy
  have hsum : Summable (fun k : ℤ => eta (y / (2 : ℝ) ^ k)) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hpart
    norm_num at hpart
  have hle := hsum.le_tsum (0 : ℤ) (fun k hk => heta.2.2.1 _)
  simpa [hpart] using hle

/-- The raw one-edge multiplier is uniformly bounded by one. -/
theorem rawMultiplier_norm_le_one {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (hY : 0 < S.Y) (D aa bb : ℕ) (hD : 0 < D)
    (hdyad : (S.d₀ : ℝ) ≤ (D : ℝ)) (t : ℤ) :
    ‖rawMultiplier F S D aa bb t‖ ≤ 1 := by
  have heta : IsCauchyCutoff F.eta := hF.2.2.2.2.1
  have hpsi : IsArcCutoff F.psi := hF.2.2.2.2.2
  by_cases ht : t = (bb : ℤ) - aa
  · by_cases hbb : F.eta ((bb : ℝ) / S.Y) = 0
    · simp [rawMultiplier, hbb]
    by_cases haa : F.eta ((aa : ℝ) / S.Y) = 0
    · simp [rawMultiplier, haa]
    have hbbRange := heta.2.1 hbb
    have haaRange := heta.2.1 haa
    have htRatio : (t : ℝ) / S.Y = (bb : ℝ) / S.Y - (aa : ℝ) / S.Y := by
      rw [ht]
      push_cast
      ring
    have hpsiOne : F.psi ((t : ℝ) / S.Y) = 1 := by
      apply hpsi.2.2
      rw [htRatio]
      constructor <;> linarith [hbbRange.1, hbbRange.2, haaRange.1, haaRange.2]
    have hscalar : 0 ≤ (S.d₀ : ℝ) / (D : ℝ) := by positivity
    have hscalarOne : (S.d₀ : ℝ) / (D : ℝ) ≤ 1 := by
      apply (div_le_one₀ (by exact_mod_cast hD)).2
      exact hdyad
    have hnorm :
        ‖rawMultiplier F S D aa bb t‖ =
          (S.d₀ : ℝ) / (D : ℝ) * F.eta ((bb : ℝ) / S.Y) *
            F.eta ((aa : ℝ) / S.Y) := by
      simp only [rawMultiplier, if_pos ht, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_one,
        abs_of_nonneg hscalar, abs_of_nonneg (heta.2.2.1 _), hpsiOne, abs_one, mul_one]
    rw [hnorm]
    calc
      _ ≤ 1 * 1 * 1 :=
        mul_le_mul
          (mul_le_mul hscalarOne (cauchyCutoff_le_one heta _)
            (heta.2.2.1 _) (by norm_num))
          (cauchyCutoff_le_one heta _) (heta.2.2.1 _) (by norm_num)
      _ = 1 := by norm_num
  · simp [rawMultiplier, ht]

/-- Fix global size and support bounds for the major-arc cutoff. -/
theorem arcCutoff_bounds {psi : ℝ → ℝ} (hpsi : IsArcCutoff psi) :
    ∃ B R : ℝ, 0 < B ∧ 4 ≤ R ∧
      (∀ t : ℝ, |psi t| ≤ B) ∧ (∀ t : ℝ, psi t ≠ 0 → |t| ≤ R) := by
  obtain ⟨B₀, hB₀⟩ := hpsi.2.1.exists_bound_of_continuous hpsi.1.continuous
  have hcompact : IsCompact (tsupport psi) := hpsi.2.1
  obtain ⟨R₀, hR₀, hRbound⟩ := hcompact.isBounded.exists_pos_norm_le
  refine ⟨max 1 B₀, max 4 R₀, lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    le_max_left _ _, ?_, ?_⟩
  · intro t
    have hb : |psi t| ≤ B₀ := by simpa only [Real.norm_eq_abs] using hB₀ t
    exact hb.trans (le_max_right _ _)
  · intro t ht
    have htsupport : t ∈ tsupport psi := subset_closure ht
    have hr : |t| ≤ R₀ := by simpa only [Real.norm_eq_abs] using hRbound t htsupport
    exact hr.trans (le_max_right _ _)

/-- Removing the scalar and eta cutoffs can only increase a comparison multiplier's norm. -/
theorem comparisonMultiplier_norm_le_kernel {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (D aa bb : ℕ) (hD : 0 < D)
    (hdyad : (S.d₀ : ℝ) ≤ (D : ℝ)) (t : ℤ) :
    ‖comparisonMultiplier F S D aa bb t‖ ≤
      ‖majorKernel S.x S.Y F.A₀ (t : ℝ) aa bb F.psi‖ := by
  have heta : IsCauchyCutoff F.eta := hF.2.2.2.2.1
  have hscalar : 0 ≤ (S.d₀ : ℝ) / (D : ℝ) := by positivity
  have hscalarOne : (S.d₀ : ℝ) / (D : ℝ) ≤ 1 :=
    (div_le_one₀ (by exact_mod_cast hD)).mpr hdyad
  have hprefix : (S.d₀ : ℝ) / (D : ℝ) * F.eta ((bb : ℝ) / S.Y) *
      F.eta ((aa : ℝ) / S.Y) ≤ 1 := by
    calc
      _ ≤ 1 * 1 * 1 :=
        mul_le_mul
          (mul_le_mul hscalarOne (cauchyCutoff_le_one heta _)
            (heta.2.2.1 _) (by norm_num))
          (cauchyCutoff_le_one heta _) (heta.2.2.1 _) (by norm_num)
      _ = 1 := by norm_num
  simp only [comparisonMultiplier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hscalar, abs_of_nonneg (heta.2.2.1 _)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hprefix
    (norm_nonneg (majorKernel S.x S.Y F.A₀ (t : ℝ) aa bb F.psi))

end ArtinPrimitiveRoots.TypeII.PD
