import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open scoped Topology
set_option autoImplicit false

/-- Weighted Cauchy inequality for the norm of a Bochner integral. -/
lemma pd7d_weighted_integral_sq (h : ℝ → ℂ) (U : ℝ → ℂ) (R : ℝ)
    (hh : Integrable h) (hU : Continuous U) (hR : 0 ≤ R)
    (hbound : ∀ ξ, ‖U ξ‖ ≤ R) :
    ‖∫ ξ : ℝ, h ξ * U ξ‖ ^ 2 ≤
      (∫ ξ : ℝ, ‖h ξ‖) * ∫ ξ : ℝ, ‖h ξ‖ * ‖U ξ‖ ^ 2 := by
  have hi := hh.mul_bdd hU.aestronglyMeasurable (ae_of_all _ hbound)
  have hAi : Integrable (fun ξ => ‖h ξ‖ * ‖U ξ‖) :=
    hh.norm.mul_bdd hU.norm.aestronglyMeasurable (ae_of_all _ fun ξ => by
      simpa only [Real.norm_eq_abs, abs_norm] using hbound ξ)
  have hBi : Integrable (fun ξ => ‖h ξ‖ * ‖U ξ‖ ^ 2) :=
    hh.norm.mul_bdd (hU.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound ξ) 2)
  let H := ∫ ξ : ℝ, ‖h ξ‖
  let A := ∫ ξ : ℝ, ‖h ξ‖ * ‖U ξ‖
  let B := ∫ ξ : ℝ, ‖h ξ‖ * ‖U ξ‖ ^ 2
  have hH : 0 ≤ H := integral_nonneg (fun _ => norm_nonneg _)
  have hA : 0 ≤ A := integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hB : 0 ≤ B := integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
  have hnorm : ‖∫ ξ : ℝ, h ξ * U ξ‖ ≤ A := by
    simpa only [norm_mul] using norm_integral_le_integral_norm (fun ξ => h ξ * U ξ)
  have hAupper : A ≤ R * H := by
    calc
      _ ≤ ∫ ξ : ℝ, R * ‖h ξ‖ := integral_mono hAi (hh.norm.const_mul _) (fun ξ => by
        calc
          ‖h ξ‖ * ‖U ξ‖ ≤ ‖h ξ‖ * R := mul_le_mul_of_nonneg_left (hbound ξ) (norm_nonneg _)
          _ = _ := mul_comm _ _)
      _ = _ := integral_const_mul _ _
  have hCS : A ^ 2 ≤ H * B := by
    by_cases hHz : H = 0
    · have hAz : A = 0 := le_antisymm (by simpa [hHz] using hAupper) hA
      simp [hHz, hAz]
    · have hHp : 0 < H := lt_of_le_of_ne hH (Ne.symm hHz)
      let a := A / H
      have hnonneg : 0 ≤ ∫ ξ : ℝ, ‖h ξ‖ * (‖U ξ‖ - a) ^ 2 :=
        integral_nonneg (fun ξ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      have hEq : (∫ ξ : ℝ, ‖h ξ‖ * (‖U ξ‖ - a) ^ 2) =
          B - 2 * a * A + a ^ 2 * H := by
        calc
          _ = ∫ ξ : ℝ, ‖h ξ‖ * ‖U ξ‖ ^ 2 -
              (2 * a) * (‖h ξ‖ * ‖U ξ‖) + a ^ 2 * ‖h ξ‖ := by
                apply integral_congr_ae
                exact ae_of_all _ fun ξ => by ring
          _ = _ := by
            have hcal := integral_add (hBi.sub (hAi.const_mul (2 * a))) (hh.norm.const_mul (a ^ 2))
            simp only [Pi.sub_apply, integral_sub hBi (hAi.const_mul (2 * a)),
              integral_const_mul] at hcal
            exact hcal
      rw [hEq] at hnonneg
      have hapos : a * H = A := by dsimp [a]; field_simp
      rw [← hapos] at hnonneg ⊢
      nlinarith [mul_nonneg hHp.le hnonneg]
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hCS

/-- Weighted Minkowski in square-integral form, with explicit boundedness and Fubini data. -/
lemma pd7d_mellin_energy_bound (h : ℝ → ℂ) (U : ℝ → ℝ → ℂ) (T R E : ℝ)
    (hh : Integrable h) (hU : Continuous (Function.uncurry U))
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hbound : ∀ ξ t, ‖U ξ t‖ ≤ R)
    (henergy : ∀ ξ : ℝ, (∫ t in (-T)..T, ‖U ξ t‖ ^ 2) ≤ E) :
    ∫ t in (-T)..T, ‖∫ ξ : ℝ, h ξ * U ξ t‖ ^ 2 ≤
      (∫ ξ : ℝ, ‖h ξ‖) ^ 2 * E := by
  let ν : Measure ℝ := volume.restrict (Set.Icc (-T) T)
  have hν : IsFiniteMeasure ν := ⟨by dsimp [ν]; simp⟩
  letI := hν
  let F := fun z : ℝ × ℝ => ‖h z.1‖ * ‖U z.1 z.2‖ ^ 2
  have hFmeas : AEStronglyMeasurable F (volume.prod ν) :=
    (hh.norm.aestronglyMeasurable.comp_fst).mul (hU.norm.pow 2).aestronglyMeasurable
  have hFint : Integrable F (volume.prod ν) := by
    apply (hh.norm.mul_prod (integrable_const (R ^ 2))).mono' hFmeas
    filter_upwards [] with z
    dsimp [F]
    rw [abs_of_nonneg (by positivity : 0 ≤ ‖h z.1‖ * ‖U z.1 z.2‖ ^ 2)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hbound z.1 z.2) 2) (norm_nonneg _)
  have hUi (t : ℝ) : Continuous (fun ξ => U ξ t) :=
    hU.comp (continuous_id.prodMk continuous_const)
  have hHi (t : ℝ) : Integrable (fun ξ => h ξ * U ξ t) :=
    hh.mul_bdd (hUi t).aestronglyMeasurable (ae_of_all _ fun ξ => hbound ξ t)
  have hHUjoint : AEStronglyMeasurable
      (fun z : ℝ × ℝ => h z.1 * U z.1 z.2) (volume.prod ν) :=
    hh.aestronglyMeasurable.comp_fst.mul hU.aestronglyMeasurable
  have hleftMeas : AEStronglyMeasurable
      (fun t => ‖∫ ξ : ℝ, h ξ * U ξ t‖ ^ 2) ν :=
    hHUjoint.prod_swap.integral_prod_right'.norm.pow 2
  have hrightInt : Integrable (fun t => (∫ ξ : ℝ, ‖h ξ‖) *
      ∫ ξ : ℝ, ‖h ξ‖ * ‖U ξ t‖ ^ 2) ν :=
    hFint.integral_prod_right.const_mul _
  have hpoint (t : ℝ) : ‖∫ ξ : ℝ, h ξ * U ξ t‖ ^ 2 ≤
      (∫ ξ : ℝ, ‖h ξ‖) * ∫ ξ : ℝ, ‖h ξ‖ * ‖U ξ t‖ ^ 2 :=
    pd7d_weighted_integral_sq h (fun ξ => U ξ t) R hh (hUi t) hR (fun ξ => hbound ξ t)
  have hleftInt : Integrable (fun t => ‖∫ ξ : ℝ, h ξ * U ξ t‖ ^ 2) ν :=
    hrightInt.mono' hleftMeas (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint t)
  have hinner (ξ : ℝ) : (∫ t, ‖U ξ t‖ ^ 2 ∂ν) ≤ E := by
    have hh := henergy ξ
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
      ← integral_Icc_eq_integral_Ioc] at hh
    exact hh
  have houter : (∫ ξ : ℝ, ‖h ξ‖ * (∫ t, ‖U ξ t‖ ^ 2 ∂ν)) ≤
      (∫ ξ : ℝ, ‖h ξ‖) * E := by
    calc
      _ ≤ ∫ ξ : ℝ, ‖h ξ‖ * E := by
        apply integral_mono
        · simpa only [F, integral_const_mul] using hFint.integral_prod_left
        · exact hh.norm.mul_const E
        · intro ξ
          exact mul_le_mul_of_nonneg_left (hinner ξ) (norm_nonneg _)
      _ = _ := integral_mul_const _ _
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    ← integral_Icc_eq_integral_Ioc]
  change (∫ t, ‖∫ ξ : ℝ, h ξ * U ξ t‖ ^ 2 ∂ν) ≤ _
  calc
    _ ≤ ∫ t, (∫ ξ : ℝ, ‖h ξ‖) * (∫ ξ : ℝ, ‖h ξ‖ * ‖U ξ t‖ ^ 2) ∂ν :=
      integral_mono hleftInt hrightInt hpoint
    _ = (∫ ξ : ℝ, ‖h ξ‖) * ∫ ξ : ℝ, ‖h ξ‖ * (∫ t, ‖U ξ t‖ ^ 2 ∂ν) := by
      rw [integral_const_mul, ← integral_integral_swap hFint]
      simp only [integral_const_mul]
    _ ≤ (∫ ξ : ℝ, ‖h ξ‖) * ((∫ ξ : ℝ, ‖h ξ‖) * E) :=
      mul_le_mul_of_nonneg_left houter (integral_nonneg (fun _ => norm_nonneg _))
    _ = _ := by ring

end ArtinPrimitiveRoots.TypeII.PD
