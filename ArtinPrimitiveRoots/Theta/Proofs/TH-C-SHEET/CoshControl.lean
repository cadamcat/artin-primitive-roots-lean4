import ArtinPrimitiveRoots.Theta.Shared
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

set_option autoImplicit false
noncomputable section

open MeasureTheory
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

/-- Base control of the cubic Bessel cosh integral on the positive axis. -/
theorem bessel_cubic_cosh_control :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 < x →
      IntegrableOn (fun t : ℝ => Real.exp (-x * Real.cosh t) *
        Real.cosh ((1 / 3 : ℝ) * t)) (Set.Ioi 0) ∧
      0 < besselK (1 / 3) x ∧
      besselK (1 / 3) x ≤ B * x ^ (-(1 / 3 : ℝ)) := by
  let B : ℝ := 1 / 2 * 2 ^ (1 / 3 : ℝ) * Real.Gamma (1 / 3)
  have hν : (0 : ℝ) < 1 / 3 := by norm_num
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro x hx
  let f : ℝ → ℝ := fun t => t ^ ((1 / 3 : ℝ) - 1) *
    Real.exp (-t - x ^ 2 / (4 * t))
  let g : ℝ → ℝ := fun t => Real.exp (-t) * t ^ ((1 / 3 : ℝ) - 1)
  have hg : IntegrableOn g (Set.Ioi 0) := Real.GammaIntegral_convergent hν
  have hfpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t := by
    intro t ht
    exact mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  have hfg : ∀ t ∈ Set.Ioi (0 : ℝ), f t ≤ g t := by
    intro t ht
    dsimp only [f, g]
    rw [mul_comm (Real.exp (-t))]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos ht _).le
    apply Real.exp_le_exp.mpr
    exact sub_le_self _ (div_nonneg (sq_nonneg x) (mul_pos (by norm_num) ht).le)
  have hfc : ContinuousOn f (Set.Ioi 0) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
    · apply ContinuousOn.rexp
      apply ContinuousOn.sub continuousOn_id.neg
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_const.mul continuousOn_id
      · intro t ht
        exact mul_ne_zero (by norm_num) (ne_of_gt ht)
  have hf : IntegrableOn f (Set.Ioi 0) := by
    apply hg.mono' (hfc.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (hfpos t ht)]
    exact hfg t ht
  have hIpos : 0 < ∫ t in Set.Ioi (0 : ℝ), f t := by
    have hsupp : Function.support f ∩ Set.Ioi 0 = Set.Ioi 0 := by
      rw [Set.inter_eq_right]
      intro t ht
      exact (hfpos t ht).ne'
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · rw [hsupp, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact (hfpos t ht).le
    · exact hf
  have hIle : (∫ t in Set.Ioi (0 : ℝ), f t) ≤ Real.Gamma (1 / 3) := by
    rw [Real.Gamma_eq_integral hν]
    apply integral_mono_ae hf hg
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hfg t ht
  have hKpos : 0 < besselK (1 / 3) x := by
    rw [besselK_eq_schlafli _ _ hx]
    exact mul_pos (mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (div_pos hx (by norm_num)) _)) hIpos
  refine ⟨Integrable.of_integral_ne_zero hKpos.ne', hKpos, ?_⟩
  rw [besselK_eq_schlafli _ _ hx]
  calc
    1 / 2 * (x / 2) ^ (-(1 / 3 : ℝ)) * (∫ t in Set.Ioi (0 : ℝ), f t) ≤
        1 / 2 * (x / 2) ^ (-(1 / 3 : ℝ)) * Real.Gamma (1 / 3) :=
      mul_le_mul_of_nonneg_left hIle (by positivity)
    _ = B * x ^ (-(1 / 3 : ℝ)) := by
      rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_inv_eq_mul, B]
      ring

end ArtinPrimitiveRoots.Proofs.thsol_smooth
