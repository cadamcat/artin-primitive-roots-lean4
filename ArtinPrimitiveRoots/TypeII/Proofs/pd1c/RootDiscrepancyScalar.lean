import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootFourierDiscrepancy

namespace ArtinPrimitiveRoots.TypeII.PD
set_option maxHeartbeats 1000000

lemma pd1c_root_log_factor (t : ℝ) (ht : 1 ≤ t) :
    1 + Real.log t ≤ 101 * t ^ (1 / 100 : ℝ) := by
  have hp : 1 ≤ t ^ (1 / 100 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hlog := Real.log_le_rpow_div (x := t) (by linarith) (by norm_num : (0 : ℝ) < 1 / 100)
  norm_num only [div_div, div_one, mul_one] at hlog
  nlinarith

lemma pd1c_root_discrepancy_scalar (CK CT u S N : ℝ)
    (hCK : 0 ≤ CK) (hCT : 0 ≤ CT) (hu : 1 ≤ u) (hS : 1 ≤ S) (hN : 0 ≤ N) :
    4 * (CK * u ^ (3 / 4 + 1 / 100 : ℝ) * S ^ (1 + 1 / 100 : ℝ)) *
      (CT * u ^ (1 / 100 : ℝ)) * (1 + Real.log (u * S)) *
      (N / (u * S) + 5 * (1 + Real.log (u * S))) ≤
    (40804 * CK * CT) * u ^ (99 / 100 : ℝ) * S ^ (2 : ℝ) * (N / u + 5) := by
  have hup : 0 < u := by linarith
  have hSp : 0 < S := by linarith
  have huS : 1 ≤ u * S := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hS)]
  let L := 1 + Real.log (u * S)
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg huS]
  have hLp : 0 ≤ L := by linarith
  have hLBound : L ≤ 101 * (u * S) ^ (1 / 100 : ℝ) := pd1c_root_log_factor _ huS
  have hL2 : L ^ 2 ≤ 101 ^ 2 * ((u * S) ^ (1 / 100 : ℝ)) ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hLp hLBound 2
  have hNDiv : N / (u * S) ≤ N / u := div_le_div_of_nonneg_left hN hup (by nlinarith)
  have hNDivPos : 0 ≤ N / u := by positivity
  have hBracket : N / (u * S) + 5 * L ≤ L * (N / u + 5) := by
    nlinarith [mul_le_mul_of_nonneg_right hL hNDivPos]
  have hPowU : (u ^ (1 / 100 : ℝ)) ^ 2 = u ^ (2 / 100 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hup.le]
    congr 1
    norm_num
  have hPowS : (S ^ (1 / 100 : ℝ)) ^ 2 = S ^ (2 / 100 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hSp.le]
    congr 1
    norm_num
  have hUP : u ^ (3 / 4 + 1 / 100 : ℝ) * u ^ (1 / 100 : ℝ) * u ^ (2 / 100 : ℝ) = u ^ (79 / 100 : ℝ) := by
    rw [← Real.rpow_add hup, ← Real.rpow_add hup]
    congr 1
    norm_num
  have hSP : S ^ (1 + 1 / 100 : ℝ) * S ^ (2 / 100 : ℝ) = S ^ (103 / 100 : ℝ) := by
    rw [← Real.rpow_add hSp]
    congr 1
    norm_num
  change 4 * (CK * u ^ (3 / 4 + 1 / 100 : ℝ) * S ^ (1 + 1 / 100 : ℝ)) *
    (CT * u ^ (1 / 100 : ℝ)) * L * (N / (u * S) + 5 * L) ≤ _
  calc
    _ ≤ 4 * (CK * u ^ (3 / 4 + 1 / 100 : ℝ) * S ^ (1 + 1 / 100 : ℝ)) *
      (CT * u ^ (1 / 100 : ℝ)) * L * (L * (N / u + 5)) :=
        mul_le_mul_of_nonneg_left hBracket (by positivity)
    _ = (4 * CK * CT) * u ^ (3 / 4 + 1 / 100 : ℝ) * u ^ (1 / 100 : ℝ) * S ^ (1 + 1 / 100 : ℝ) * L ^ 2 * (N / u + 5) := by ring
    _ ≤ (4 * CK * CT) * u ^ (3 / 4 + 1 / 100 : ℝ) * u ^ (1 / 100 : ℝ) * S ^ (1 + 1 / 100 : ℝ) *
        (101 ^ 2 * ((u * S) ^ (1 / 100 : ℝ)) ^ 2) * (N / u + 5) := by
      gcongr
    _ = (40804 * CK * CT) * u ^ (79 / 100 : ℝ) * S ^ (103 / 100 : ℝ) * (N / u + 5) := by
      rw [Real.mul_rpow hup.le hSp.le, mul_pow, hPowU, hPowS]
      calc
        _ = (40804 * CK * CT) * (u ^ (3 / 4 + 1 / 100 : ℝ) * u ^ (1 / 100 : ℝ) * u ^ (2 / 100 : ℝ)) *
          (S ^ (1 + 1 / 100 : ℝ) * S ^ (2 / 100 : ℝ)) * (N / u + 5) := by ring
        _ = _ := by rw [hUP, hSP]
    _ ≤ _ := by
      gcongr <;> norm_num

end ArtinPrimitiveRoots.TypeII.PD
