import ArtinPrimitiveRoots.Theta.LocalInt

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_sheets

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]

/-- Normalized additive mass of a local ball at a realized positive radius. -/
theorem finite_ball_mass {v : FinPlace F} (μ : LocHaar v) (y : (v.adicCompletion F)ˣ) :
    μ.μ.real (Metric.closedBall (0 : v.adicCompletion F) (absFin v y)) = absFin v y := by
  let K := v.adicCompletion F
  let B := Metric.closedBall (0 : K) (absFin v y)
  let O := Metric.closedBall (0 : K) 1
  have hO : O = (v.adicCompletionIntegers F : Set K) :=
    (Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)).symm
  have hnorm : 0 < ‖(y : K)‖ := norm_pos_iff.mpr y.ne_zero
  have hpre (x : K) : (y : K) * x ∈ B ↔ x ∈ O := by
    simp only [B, O, Metric.mem_closedBall, dist_zero_right, norm_mul, absFin_eq_norm]
    constructor
    · intro hx
      nlinarith
    · intro hx
      nlinarith
  have hind (x : K) : B.indicator (fun _ => (1 : ℝ)) ((y : K) * x) =
      O.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ O
    · rw [Set.indicator_of_mem ((hpre x).mpr hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx ((hpre x).mp h)), Set.indicator_of_notMem hx]
  have hmass : (absFin v y)⁻¹ * μ.μ.real B = 1 := by
    calc
      _ = ∫ x, B.indicator (fun _ => (1 : ℝ)) ((y : K) * x) ∂μ.μ := by
        rw [μ.integral_comp_mul,
          integral_indicator_const (1 : ℝ) (show MeasurableSet B from measurableSet_closedBall)]
        simp only [smul_eq_mul, mul_one]
      _ = ∫ x, O.indicator (fun _ => (1 : ℝ)) x ∂μ.μ := by
        simp only [hind]
      _ = μ.μ.real O := by
        simpa only [smul_eq_mul, mul_one] using
          (integral_indicator_const (μ := μ.μ) (1 : ℝ)
            (show MeasurableSet O from measurableSet_closedBall))
      _ = 1 := by rw [hO, measureReal_def, μ.norm_O]; simp
  change μ.μ.real B = absFin v y
  have hy : absFin v y ≠ 0 := (absFin_pos y.ne_zero).ne'
  calc
    _ = (absFin v y * (absFin v y)⁻¹) * μ.μ.real B := by rw [mul_inv_cancel₀ hy, one_mul]
    _ = absFin v y * 1 := by rw [mul_assoc, hmass]
    _ = _ := mul_one _

end ArtinPrimitiveRoots.Proofs.thsol_sheets
