import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.DeligneGrowth

set_option autoImplicit false

open Set Complex

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- Bounded shifts of the Deligne factors have absolute polynomial ratio bounds. -/
theorem deligne_ratio_on_fixed_strips
    (hdigamma : ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, 1 ≤ u.re → u.re ≤ 10 →
      ‖deriv Complex.Gamma u / Complex.Gamma u‖ ≤ C * Real.log (|u.im| + 2)) :
    ∃ A : ℝ, 0 < A ∧
      (∀ z w : ℂ, 2 ≤ z.re → z.re ≤ 14 → 2 ≤ w.re → w.re ≤ 14 → ‖w - z‖ ≤ 12 →
        ‖Complex.Gammaℝ w / Complex.Gammaℝ z‖ ≤
          Real.exp (A * Real.log (|z.im| + 14))) ∧
      (∀ z w : ℂ, 1 ≤ z.re → z.re ≤ 10 → 1 ≤ w.re → w.re ≤ 10 → ‖w - z‖ ≤ 12 →
        ‖Complex.Gammaℂ w / Complex.Gammaℂ z‖ ≤
          Real.exp (A * Real.log (|z.im| + 14))) := by
  obtain ⟨B, hB, hgamma⟩ := gamma_ratio_on_strip
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 12) hdigamma
  let L : ℝ := 12 * |Real.log Real.pi| + 12 * |Real.log (2 * Real.pi)|
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hlog14 : 0 < Real.log (14 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨B + L / Real.log 14 + 1, by positivity, ?_⟩
  have hpower {p : ℝ} (hp : 0 < p) (u v : ℂ) (huv : |u.re - v.re| ≤ 12) :
      ‖(p : ℂ) ^ u / (p : ℂ) ^ v‖ ≤ Real.exp (12 * |Real.log p|) := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hp,
      Complex.norm_cpow_eq_rpow_re_of_pos hp, Real.rpow_def_of_pos hp,
      Real.rpow_def_of_pos hp, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    calc
      Real.log p * u.re - Real.log p * v.re = Real.log p * (u.re - v.re) := by ring
      _ ≤ |Real.log p * (u.re - v.re)| := le_abs_self _
      _ = |Real.log p| * |u.re - v.re| := abs_mul _ _
      _ ≤ |Real.log p| * 12 := mul_le_mul_of_nonneg_left huv (abs_nonneg _)
      _ = 12 * |Real.log p| := by ring
  have hfinal (t : ℝ) : Real.exp L * Real.exp (B * Real.log (|t| + 14)) ≤
      Real.exp ((B + L / Real.log 14 + 1) * Real.log (|t| + 14)) := by
    have hlog : Real.log (14 : ℝ) ≤ Real.log (|t| + 14) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    have hterm : L ≤ (L / Real.log 14) * Real.log (|t| + 14) := by
      calc
        L = (L / Real.log 14) * Real.log 14 := by field_simp [hlog14.ne']
        _ ≤ (L / Real.log 14) * Real.log (|t| + 14) :=
          mul_le_mul_of_nonneg_left hlog (div_nonneg hL hlog14.le)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hlog14.le]
  constructor
  · intro z w hza hzb hwa hwb hzw
    have hzarg : 1 ≤ (z / 2).re ∧ (z / 2).re ≤ 10 := by
      norm_num [Complex.div_ofNat_re]
      constructor <;> linarith
    have hwarg : 1 ≤ (w / 2).re ∧ (w / 2).re ≤ 10 := by
      norm_num [Complex.div_ofNat_re]
      constructor <;> linarith
    have hdist : ‖w / 2 - z / 2‖ ≤ 12 := by
      have heq : ‖w / 2 - z / 2‖ = ‖w - z‖ / 2 := by rw [← sub_div]; simp
      rw [heq]
      linarith [norm_nonneg (w - z)]
    have him : |(z / 2).im| ≤ |z.im| := by
      simp only [Complex.div_ofNat_im, abs_div]
      norm_num
    have hgam : ‖Complex.Gamma (w / 2) / Complex.Gamma (z / 2)‖ ≤
        Real.exp (B * Real.log (|z.im| + 14)) := by
      refine (hgamma _ _ hzarg.1 hzarg.2 hwarg.1 hwarg.2 hdist).trans
        (Real.exp_le_exp.mpr ?_)
      apply mul_le_mul_of_nonneg_left _ hB.le
      apply Real.log_le_log (by positivity)
      linarith
    have hpow : ‖(Real.pi : ℂ) ^ (-w / 2) / (Real.pi : ℂ) ^ (-z / 2)‖ ≤
        Real.exp L := by
      have hdiff : |(-w / 2).re - (-z / 2).re| ≤ 12 := by
        apply abs_le.mpr
        norm_num [Complex.div_ofNat_re]
        constructor <;> linarith
      refine (hpower Real.pi_pos _ _ hdiff).trans (Real.exp_le_exp.mpr ?_)
      dsimp [L]
      linarith [abs_nonneg (Real.log (2 * Real.pi))]
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, mul_div_mul_comm, norm_mul]
    exact (mul_le_mul hpow hgam (norm_nonneg _) (Real.exp_pos _).le).trans (hfinal z.im)
  · intro z w hza hzb hwa hwb hzw
    have hgam : ‖Complex.Gamma w / Complex.Gamma z‖ ≤
        Real.exp (B * Real.log (|z.im| + 14)) := by
      simpa only [show (12 : ℝ) + 2 = 14 by norm_num, add_assoc] using
        hgamma z w hza hzb hwa hwb hzw
    have hpow : ‖(2 * (Real.pi : ℂ)) ^ (-w) / (2 * (Real.pi : ℂ)) ^ (-z)‖ ≤
        Real.exp L := by
      have hdiff : |(-w).re - (-z).re| ≤ 12 := by
        apply abs_le.mpr
        simp only [Complex.neg_re]
        constructor <;> linarith
      have hp : (0 : ℝ) < 2 * Real.pi := by positivity
      have hh := hpower hp (-w) (-z) hdiff
      have heq : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by push_cast; rfl
      rw [heq] at hh
      refine hh.trans (Real.exp_le_exp.mpr ?_)
      dsimp [L]
      linarith [abs_nonneg (Real.log Real.pi)]
    rw [Complex.Gammaℂ_def, Complex.Gammaℂ_def, mul_div_mul_comm,
      mul_div_mul_left _ _ (two_ne_zero : (2 : ℂ) ≠ 0), norm_mul]
    exact (mul_le_mul hpow hgam (norm_nonneg _) (Real.exp_pos _).le).trans (hfinal z.im)

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
