import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ArtinPrimitiveRoots.Proofs.r_impl_muse

open MeasureTheory
open scoped BigOperators

/-- The reciprocal logarithmic kernel has at most logarithmic mass in each coordinate. -/
theorem continuous_reciprocal_box_mass (n : ℕ) (Y B : ℝ)
    (hY : 2 ≤ Y) (hB : 1 ≤ B) :
    (∫ t in Set.univ.pi (fun _ : Fin n => Set.Icc Y B),
      ∏ i : Fin n, (1 / (t i * Real.log (t i)) : ℝ)) ≤
      (Real.log B / Real.log 2) ^ n := by
  let f : ℝ → ℝ := fun t => 1 / (t * Real.log t)
  let q : ℝ := ∫ t in Set.Icc Y B, f t
  have hY1 : 1 < Y := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hY
  have hlogY : 0 < Real.log Y := Real.log_pos hY1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hq0 : 0 ≤ q := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht1 : 1 < t := lt_of_lt_of_le hY1 ht.1
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have hlogt : 0 < Real.log t := Real.log_pos ht1
    exact (one_div_pos.mpr (mul_pos ht0 hlogt)).le
  have hq : q ≤ Real.log B / Real.log 2 := by
    by_cases hYB : Y ≤ B
    · have hB1 : 1 < B := lt_of_lt_of_le hY1 hYB
      have hlogBpos : 0 < Real.log B := Real.log_pos hB1
      have hEq : q = Real.log (Real.log B / Real.log Y) := by
        change (∫ t in Set.Icc Y B, 1 / (t * Real.log t)) = _
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hYB]
        calc
          _ = Real.log (Real.log B) - Real.log (Real.log Y) := by
            simpa only [one_div, div_eq_mul_inv, mul_inv_rev, mul_comm, one_mul] using
              integral_inv_div_log hY1 hB1
          _ = Real.log (Real.log B / Real.log Y) :=
            (Real.log_div (ne_of_gt hlogBpos) (ne_of_gt hlogY)).symm
      have hlogLower : Real.log (2 : ℝ) ≤ Real.log Y :=
        Real.log_le_log (by norm_num) hY
      rw [hEq]
      calc
        _ ≤ Real.log B / Real.log Y - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hlogBpos hlogY)
        _ ≤ Real.log B / Real.log Y := by linarith
        _ ≤ Real.log B / Real.log 2 :=
          div_le_div_of_nonneg_left hlogB hlog2 hlogLower
    · have hEmpty : Set.Icc Y B = ∅ := Set.Icc_eq_empty_of_lt (lt_of_not_ge hYB)
      have hZero : q = 0 := by simp only [q, hEmpty, Measure.restrict_empty, integral_zero_measure]
      rw [hZero]
      exact div_nonneg hlogB hlog2.le
  have hProduct :
      (∫ t in Set.univ.pi (fun _ : Fin n => Set.Icc Y B),
        ∏ i : Fin n, (1 / (t i * Real.log (t i)) : ℝ)) = q ^ n := by
    rw [volume_pi, Measure.restrict_pi_pi]
    simpa only [q, f, Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin n)
        (μ := volume.restrict (Set.Icc Y B)) f)
  rw [hProduct]
  exact pow_le_pow_left₀ hq0 hq n

end ArtinPrimitiveRoots.Proofs.r_impl_muse
