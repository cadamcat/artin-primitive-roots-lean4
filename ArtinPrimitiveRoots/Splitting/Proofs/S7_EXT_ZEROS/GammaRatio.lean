import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.Growth
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

set_option autoImplicit false

open Set Complex

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- Digamma control on a positive strip gives polynomial bounds for bounded Gamma shifts. -/
theorem gamma_ratio_on_strip {a b L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (hdigamma : ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, a ≤ u.re → u.re ≤ b →
      ‖deriv Complex.Gamma u / Complex.Gamma u‖ ≤ C * Real.log (|u.im| + 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ z w : ℂ,
      a ≤ z.re → z.re ≤ b → a ≤ w.re → w.re ≤ b → ‖w - z‖ ≤ L →
      ‖Complex.Gamma w / Complex.Gamma z‖ ≤
        Real.exp (A * Real.log (|z.im| + L + 2)) := by
  obtain ⟨C, hC, hdigamma⟩ := hdigamma
  refine ⟨C * (L + 1) + 1, by positivity, ?_⟩
  intro z w hza hzb hwa hwb hzw
  have hre (u : ℂ) (hu : u ∈ segment ℝ z w) : a ≤ u.re ∧ u.re ≤ b := by
    rw [segment_eq_image ℝ z w] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    simp only [Complex.real_smul, Complex.add_re, Complex.re_ofReal_mul]
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hza ht1,
        mul_le_mul_of_nonneg_left hwa ht.1]
    · nlinarith [mul_le_mul_of_nonneg_left hzb ht1,
        mul_le_mul_of_nonneg_left hwb ht.1]
  have hdist (u : ℂ) (hu : u ∈ segment ℝ z w) : ‖u - z‖ ≤ L := by
    rw [segment_eq_image' ℝ z w] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc
      t * ‖w - z‖ ≤ 1 * ‖w - z‖ :=
        mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ ≤ L := by simpa only [one_mul] using hzw
  have him (u : ℂ) (hu : u ∈ segment ℝ z w) : |u.im| ≤ |z.im| + L := by
    calc
      |u.im| = |(u - z).im + z.im| := by simp
      _ ≤ |(u - z).im| + |z.im| := abs_add_le _ _
      _ ≤ L + |z.im| := by
        linarith [(Complex.abs_im_le_norm (u - z)).trans (hdist u hu)]
      _ = |z.im| + L := add_comm _ _
  have hdiff (u : ℂ) (hu : u ∈ segment ℝ z w) :
      DifferentiableAt ℂ Complex.Gamma u := by
    apply Complex.differentiableAt_Gamma u
    intro n hn
    have hru : u.re = -(n : ℝ) := by simpa using congrArg Complex.re hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [(hre u hu).1]
  have hne (u : ℂ) (hu : u ∈ segment ℝ z w) : Complex.Gamma u ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (lt_of_lt_of_le ha (hre u hu).1)
  have hlogder (u : ℂ) (hu : u ∈ segment ℝ z w) :
      ‖deriv Complex.Gamma u / Complex.Gamma u‖ ≤ C * Real.log (|z.im| + L + 2) := by
    refine (hdigamma u (hre u hu).1 (hre u hu).2).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.log_le_log (by positivity)
    linarith [him u hu]
  have hlog : 0 ≤ Real.log (|z.im| + L + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg z.im])
  refine (norm_ratio_le_exp_of_logDeriv_bound hdiff hne hlogder).trans ?_
  apply Real.exp_le_exp.mpr
  calc
    (C * Real.log (|z.im| + L + 2)) * ‖w - z‖ =
        (C * ‖w - z‖) * Real.log (|z.im| + L + 2) := by ring
    _ ≤ (C * L) * Real.log (|z.im| + L + 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzw hC.le) hlog
    _ ≤ (C * (L + 1) + 1) * Real.log (|z.im| + L + 2) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hC.le]) hlog

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
