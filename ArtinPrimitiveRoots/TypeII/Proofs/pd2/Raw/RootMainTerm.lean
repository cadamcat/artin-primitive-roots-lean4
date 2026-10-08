import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootRowCount

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_rootAverageConstant : ℝ := 2 + (32 + 6 * Real.log 2) / Real.log 2

lemma pd2a_rootAverageConstant_pos : 0 < pd2a_rootAverageConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  dsimp [pd2a_rootAverageConstant]
  positivity

lemma pd2a_rootEuler_scaled_average (U : ℝ) (hU : 2 ≤ U) (S : ℕ) (hS : 0 < S) (a : ZMod S)
    (l r : ℝ) (hl : 1 ≤ l) (hlr : l ≤ r) (hr : r ≤ 16) :
    |(∑ u ∈ pd2a_natClosedInterval (l * U) (r * U), if (u : ZMod S) = a then pd2a_rootEulerFactor u S else 0) -
      (U * (r - l) / S) * pd2a_rootEulerConstant S| ≤ pd2a_rootAverageConstant * Real.log (2 * U) := by
  have hUp : 0 < U := by linarith
  have hSp : 0 < (S : ℝ) := by exact_mod_cast hS
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hA : 1 ≤ l * U := by nlinarith
  have hAB : l * U ≤ r * U := mul_le_mul_of_nonneg_right hlr hUp.le
  have hB : 0 ≤ r * U := by linarith
  let N := ⌊r * U⌋₊
  have hNlower : U / 2 ≤ (N : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (r * U)
    have hru : U ≤ r * U := by nlinarith
    linarith
  have hNp : 0 < (N : ℝ) := by linarith
  have hNupper : (N : ℝ) ≤ 16 * U := (Nat.floor_le hB).trans (by nlinarith)
  have hLogN : Real.log (N : ℝ) ≤ Real.log (16 * U) := Real.log_le_log hNp hNupper
  have hW : 0 ≤ U * (r - l) := mul_nonneg hUp.le (sub_nonneg.mpr hlr)
  have hWupper : U * (r - l) / S ≤ 15 * U := by
    have hDiv : U * (r - l) / S ≤ U * (r - l) := by
      have h := div_le_div_of_nonneg_left hW (by norm_num : (0 : ℝ) < 1) hS1
      simpa only [div_one] using h
    exact hDiv.trans (by nlinarith)
  have hTail : (U * (r - l) / S) * (1 / (N : ℝ)) ≤ 30 := by
    rw [mul_one_div, div_le_iff₀ hNp]
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLogU : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
  have hLog2U : Real.log 2 ≤ Real.log (2 * U) := by
    rw [Real.log_mul (by norm_num) hUp.ne']
    linarith
  have hLogs : Real.log (16 * U) = Real.log (2 * U) + 3 * Real.log 2 := by
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hUp.ne', Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hUp.ne']
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      calc
        Real.log (16 : ℝ) = Real.log ((2 : ℝ) ^ 4) := by norm_num
        _ = 4 * Real.log 2 := Real.log_pow (2 : ℝ) 4
    rw [h16]
    ring
  have hConst : 32 + 2 * Real.log (16 * U) ≤ pd2a_rootAverageConstant * Real.log (2 * U) := by
    have hNum : 0 ≤ (32 + 6 * Real.log 2) / Real.log 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hLog2U hNum
    have heq : ((32 + 6 * Real.log 2) / Real.log 2) * Real.log 2 = 32 + 6 * Real.log 2 :=
      div_mul_cancel₀ _ hlog2.ne'
    rw [heq] at hmul
    rw [hLogs]
    dsimp [pd2a_rootAverageConstant]
    nlinarith
  have hAvg := pd2a_rootEuler_progression_average S hS a (l * U) (r * U) hA hAB
  have hMainEq : (r * U - l * U) / (S : ℝ) = U * (r - l) / S := by ring
  rw [hMainEq] at hAvg
  exact hAvg.trans ((add_le_add (show 2 * (1 + Real.log (N : ℝ)) ≤ 2 * (1 + Real.log (16 * U)) by linarith) hTail).trans (by linarith [hConst]))

lemma pd2a_root_main_term_identity (U V : ℝ) (S : ℕ) (hS : 0 < S) (hSq : Squarefree S)
    (d₁ d₂ d₃ : ℝ) :
    (V * d₂ * d₃ / (S : ℝ) ^ 2) * ((U * d₁ / S) * pd2a_rootEulerConstant S) =
      U * V * d₁ * d₂ * d₃ / ((Real.pi ^ 2 / 6) * (sl2Card S hS : ℝ)) := by
  let P := ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℝ) ^ 2)
  have hSp : 0 < (S : ℝ) := by exact_mod_cast hS
  have hCard : (sl2Card S hS : ℝ) = (S : ℝ) ^ 3 * P := pd2a_sl2Card_squarefree_real S hS hSq
  have hCardPos : 0 < (sl2Card S hS : ℝ) := by exact_mod_cast pd2a_sl2Card_pos S hS
  have hP : P ≠ 0 := by intro hp; rw [hp, mul_zero] at hCard; linarith
  have hZ : Real.pi ^ 2 / 6 ≠ 0 := by positivity
  rw [pd2a_rootEulerConstant_value S hS, hCard]
  change (V * d₂ * d₃ / (S : ℝ) ^ 2) * ((U * d₁ / S) * ((Real.pi ^ 2 / 6)⁻¹ * P⁻¹)) = _
  field_simp

end ArtinPrimitiveRoots.TypeII.PD
