import ArtinPrimitiveRoots.Proofs.th_res_whit_b.ComplexArch
import ArtinPrimitiveRoots.Theta.Shared
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

private def schlafliOneThirdIntegrand (x t : ℝ) : ℝ :=
  t ^ (-(2 / 3 : ℝ)) * Real.exp (-t - x ^ 2 / (4 * t))

private theorem schlafliOneThird_integrableOn (x : ℝ) (hx : 0 < x) :
    IntegrableOn (schlafliOneThirdIntegrand x) (Set.Ioi (0 : ℝ)) volume := by
  let c : ℝ := x ^ 2 / 4
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall : IntegrableOn (schlafliOneThirdIntegrand x) (Set.Ioc (0 : ℝ) 1) volume := by
    have hconst : IntegrableOn (fun _ : ℝ => 1 / c) (Set.Ioc (0 : ℝ) 1) volume := by
      exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
    have hmeas : AEStronglyMeasurable (schlafliOneThirdIntegrand x)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      change AEStronglyMeasurable
        (fun t : ℝ => t ^ (-(2 / 3 : ℝ)) * Real.exp (-t - x ^ 2 / (4 * t))) _
      fun_prop
    have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        ‖schlafliOneThirdIntegrand x t‖ ≤ 1 / c := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have htpos : 0 < t := ht.1
      have htle : t ≤ 1 := ht.2
      have hypos : 0 < c / t := div_pos hc htpos
      have hyexp : c / t ≤ Real.exp (c / t) := by
        have hh := Real.add_one_le_exp (c / t)
        linarith
      have hExpInv : Real.exp (-(c / t)) ≤ t / c := by
        calc
          Real.exp (-(c / t)) = 1 / Real.exp (c / t) := by rw [Real.exp_neg]; simp
          _ ≤ 1 / (c / t) := one_div_le_one_div_of_le hypos hyexp
          _ = t / c := by field_simp
      have hExpNeg : Real.exp (-t) ≤ 1 := by
        calc
          Real.exp (-t) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
          _ = 1 := by norm_num
      have hExpTotal : Real.exp (-t - c / t) ≤ t / c := by
        rw [show -t - c / t = (-t) + (-(c / t)) by ring, Real.exp_add]
        calc
          Real.exp (-t) * Real.exp (-(c / t)) ≤ 1 * (t / c) :=
            mul_le_mul hExpNeg hExpInv (Real.exp_nonneg _) (by positivity)
          _ = t / c := by ring
      have hpowprod : t ^ (-(2 / 3 : ℝ)) * t = t ^ (1 / 3 : ℝ) := by
        calc
          t ^ (-(2 / 3 : ℝ)) * t = t ^ (-(2 / 3 : ℝ)) * t ^ (1 : ℝ) := by simp
          _ = t ^ (-(2 / 3 : ℝ) + 1) := by rw [← Real.rpow_add htpos]
          _ = t ^ (1 / 3 : ℝ) := by congr 1 <;> ring
      have hpowle : t ^ (1 / 3 : ℝ) ≤ 1 := by
        calc
          t ^ (1 / 3 : ℝ) ≤ (1 : ℝ) ^ (1 / 3 : ℝ) :=
            Real.rpow_le_rpow htpos.le htle (by norm_num)
          _ = 1 := by norm_num
      have hreal : schlafliOneThirdIntegrand x t ≤ 1 / c := by
        dsimp [schlafliOneThirdIntegrand, c]
        calc
          t ^ (-(2 / 3 : ℝ)) * Real.exp (-t - x ^ 2 / (4 * t)) ≤
              t ^ (-(2 / 3 : ℝ)) * (t / c) := by
                rw [show x ^ 2 / (4 * t) = c / t by dsimp [c]; ring]
                exact mul_le_mul_of_nonneg_left hExpTotal (Real.rpow_nonneg htpos.le _)
          _ = (1 / c) * t ^ (1 / 3 : ℝ) := by
            calc
              t ^ (-(2 / 3 : ℝ)) * (t / c) = (1 / c) *
                  (t ^ (-(2 / 3 : ℝ)) * t) := by ring
              _ = (1 / c) * t ^ (1 / 3 : ℝ) := by rw [hpowprod]
          _ ≤ 1 / c := by
            exact mul_le_of_le_one_right (by positivity) hpowle
      have hnonneg : 0 ≤ schlafliOneThirdIntegrand x t := by
        dsimp [schlafliOneThirdIntegrand]
        exact mul_nonneg (Real.rpow_nonneg htpos.le _) (Real.exp_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hreal
    exact hconst.mono' hmeas hbound
  have htail : IntegrableOn (schlafliOneThirdIntegrand x) (Set.Ioi 1) volume := by
    have hconst : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 1) volume :=
      integrableOn_exp_neg_Ioi 1
    have hmeas : AEStronglyMeasurable (schlafliOneThirdIntegrand x)
        (volume.restrict (Set.Ioi 1)) := by
      change AEStronglyMeasurable
        (fun t : ℝ => t ^ (-(2 / 3 : ℝ)) * Real.exp (-t - x ^ 2 / (4 * t))) _
      fun_prop
    have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi 1)),
        ‖schlafliOneThirdIntegrand x t‖ ≤ Real.exp (-t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := lt_trans zero_lt_one ht
      have hpow : t ^ (-(2 / 3 : ℝ)) ≤ 1 :=
        calc
          t ^ (-(2 / 3 : ℝ)) ≤ t ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (le_of_lt ht) (by norm_num)
          _ = 1 := by simp
      have hexp : Real.exp (-t - x ^ 2 / (4 * t)) ≤ Real.exp (-t) := by
        apply Real.exp_le_exp.mpr
        have hden : 0 < 4 * t := by positivity
        have hfrac : 0 < x ^ 2 / (4 * t) := div_pos (by positivity) hden
        linarith
      have hnonneg : 0 ≤ schlafliOneThirdIntegrand x t := by
        dsimp [schlafliOneThirdIntegrand]
        exact mul_nonneg (Real.rpow_nonneg htpos.le _) (Real.exp_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      dsimp [schlafliOneThirdIntegrand]
      calc
        t ^ (-(2 / 3 : ℝ)) * Real.exp (-t - x ^ 2 / (4 * t)) ≤
            1 * Real.exp (-t) := mul_le_mul hpow hexp (Real.exp_nonneg _) (by norm_num)
        _ = Real.exp (-t) := by ring
    exact hconst.mono' hmeas hbound
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hsmall.union htail

theorem besselK_oneThird_pos {x : ℝ} (hx : 0 < x) : 0 < besselK (1 / 3) x := by
  rw [besselK_eq_schlafli (1 / 3) x hx]
  let f := schlafliOneThirdIntegrand x
  have hfi : IntegrableOn f (Set.Ioi (0 : ℝ)) volume := schlafliOneThird_integrableOn x hx
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    dsimp [f, schlafliOneThirdIntegrand]
    exact mul_nonneg (Real.rpow_nonneg htpos.le _) (Real.exp_nonneg _)
  have hsupp : 0 < volume (Function.support f ∩ Set.Ioi (0 : ℝ)) := by
    have hsub : Set.Ioc (1 : ℝ) 2 ⊆ Function.support f ∩ Set.Ioi 0 := by
      intro t ht
      constructor
      · simp only [Function.mem_support]
        have htpos : 0 < t := lt_trans zero_lt_one ht.1
        have hpos : 0 < schlafliOneThirdIntegrand x t := by
          dsimp [schlafliOneThirdIntegrand]
          exact mul_pos (Real.rpow_pos_of_pos htpos _) (Real.exp_pos _)
        simpa [f] using ne_of_gt hpos
      · exact lt_trans zero_lt_one ht.1
    have hmeasure : 0 < volume (Set.Ioc (1 : ℝ) 2) := by simp
    exact lt_of_lt_of_le hmeasure (measure_mono hsub)
  have hIntegralPos : 0 < ∫ t in Set.Ioi (0 : ℝ), f t ∂volume :=
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hfi).2 hsupp
  have hc : 0 < (x / 2 : ℝ) := by positivity
  have hfactor : 0 < (1 / 2 : ℝ) * (x / 2) ^ (-(1 / 3 : ℝ)) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hc _)
  have hIntegralPos' : 0 < ∫ t in Set.Ioi (0 : ℝ),
      t ^ ((1 / 3 : ℝ) - 1) * Real.exp (-t - x ^ 2 / (4 * t)) ∂volume := by
    have heq : (fun t : ℝ => t ^ ((1 / 3 : ℝ) - 1) *
        Real.exp (-t - x ^ 2 / (4 * t))) = f := by
      funext t
      rw [show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by ring]
      rfl
    rw [heq]
    exact hIntegralPos
  simpa using mul_pos hfactor hIntegralPos'

end ArtinPrimitiveRoots.A1.Theta
