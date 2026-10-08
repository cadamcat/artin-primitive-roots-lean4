import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
set_option autoImplicit false

lemma pd7d_endpoint_product_energy_le (Q E : ℝ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hQ : Continuous Q) (hE : Continuous E)
    (hQenergy : (∫ t in a..b, ‖Q t‖ ^ 2) ≤ C)
    (hEenergy : (∫ t in a..b, ‖E t‖ ^ 2) ≤ C) :
    (∫ t in a..b, ‖Q t * E t‖) ≤ C := by
  have hQi : IntervalIntegrable (fun t => ‖Q t‖ ^ 2) volume a b := (hQ.norm.pow 2).intervalIntegrable _ _
  have hEi : IntervalIntegrable (fun t => ‖E t‖ ^ 2) volume a b := (hE.norm.pow 2).intervalIntegrable _ _
  have hpoint (t : ℝ) : ‖Q t * E t‖ ≤ (‖Q t‖ ^ 2 + ‖E t‖ ^ 2) / 2 := by
    rw [norm_mul]
    nlinarith [sq_nonneg (‖Q t‖ - ‖E t‖)]
  calc
    _ ≤ ∫ t in a..b, (‖Q t‖ ^ 2 + ‖E t‖ ^ 2) / 2 :=
      intervalIntegral.integral_mono_on hab ((hQ.mul hE).norm.intervalIntegrable _ _)
        ((hQi.add hEi).div_const 2) (fun t _ => hpoint t)
    _ = ((∫ t in a..b, ‖Q t‖ ^ 2) + ∫ t in a..b, ‖E t‖ ^ 2) / 2 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add hQi hEi]
    _ ≤ _ := by linarith

end ArtinPrimitiveRoots.TypeII.PD
