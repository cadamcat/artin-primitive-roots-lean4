import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootEulerReindex

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Proofs.pd0
set_option maxHeartbeats 1000000

lemma pd1c_rootEuler_progression_average (S : ℕ) (hS : 0 < S) (a : ZMod S)
    (A B : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    |(∑ u ∈ pd1c_natClosedInterval A B, if (u : ZMod S) = a then pd1c_rootEulerFactor u S else 0) -
      ((B - A) / S) * pd1c_rootEulerConstant S| ≤
        2 * (1 + Real.log (⌊B⌋₊ : ℝ)) + ((B - A) / S) * (1 / (⌊B⌋₊ : ℝ)) := by
  let N := ⌊B⌋₊
  let W := (B - A) / (S : ℝ)
  let I := pd1c_natClosedInterval A B
  let t := fun d : ℕ => if Nat.Coprime d S then
    (ArithmeticFunction.moebius d : ℝ) / d * ((I.filter (fun u => d ∣ u ∧ (u : ZMod S) = a)).card : ℝ) else 0
  have hN : 0 < N := by
    have hB0 : 0 ≤ B := by linarith
    have hN1 : 1 ≤ N := (Nat.le_floor_iff hB0).mpr (by norm_num only [Nat.cast_one]; linarith)
    omega
  have hSr : 0 < (S : ℝ) := by exact_mod_cast hS
  have hW : 0 ≤ W := div_nonneg (sub_nonneg.mpr hAB) hSr.le
  have hReindex : (∑ u ∈ I, if (u : ZMod S) = a then pd1c_rootEulerFactor u S else 0) =
      ∑ d ∈ Finset.range (N + 1), t d := pd1c_rootEuler_reindex S a A B hA hAB
  have hpoint : ∀ d ∈ Finset.range (N + 1), |t d - W * pd1c_rootEulerCoefficient S d| ≤ 2 / (d : ℝ) := by
    intro d hd
    by_cases hd0 : d = 0
    · subst d
      simp [t, pd1c_rootEulerCoefficient]
    · have hdp : 0 < d := Nat.pos_of_ne_zero hd0
      have hdr : 0 < (d : ℝ) := by exact_mod_cast hdp
      by_cases hc : Nat.Coprime d S
      · have hCount := pd1c_crt_progression_error d S hdp hS hc a A B (by linarith) hAB
        have hDen : (B - A) / ((d * S : ℕ) : ℝ) = W / d := by dsimp [W]; push_cast; ring
        rw [hDen] at hCount
        have hEq : t d - W * pd1c_rootEulerCoefficient S d =
            ((ArithmeticFunction.moebius d : ℝ) / d) *
              (((I.filter (fun u => d ∣ u ∧ (u : ZMod S) = a)).card : ℝ) - W / d) := by
          dsimp [t, pd1c_rootEulerCoefficient]
          rw [if_pos hc, if_pos hc]
          field_simp
        have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
        have hweight : |(ArithmeticFunction.moebius d : ℝ) / d| ≤ 1 / (d : ℝ) := by
          rw [abs_div, abs_of_pos hdr]
          exact div_le_div_of_nonneg_right hμ hdr.le
        rw [hEq, abs_mul]
        exact (mul_le_mul hweight hCount (abs_nonneg _) (by positivity)).trans_eq (by ring)
      · have hcopFalse : ¬Nat.gcd d S = 1 := hc
        simp only [t, pd1c_rootEulerCoefficient, Nat.Coprime, hcopFalse, ite_false, mul_zero, sub_self, abs_zero]
        positivity
  have hHarmonic : (∑ d ∈ Finset.range (N + 1), 1 / (d : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
    have hSet : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext d
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hSet, Finset.sum_insert (by simp), Nat.cast_zero, div_zero, zero_add]
    simpa only [positiveRange_eq_Icc, one_div] using harmonicRange_le_one_add_log N
  have hFinite : |(∑ d ∈ Finset.range (N + 1), t d) - W * (∑ d ∈ Finset.range (N + 1), pd1c_rootEulerCoefficient S d)| ≤
      2 * (1 + Real.log (N : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ d ∈ Finset.range (N + 1), |t d - W * pd1c_rootEulerCoefficient S d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.range (N + 1), 2 / (d : ℝ) := Finset.sum_le_sum fun d hd => hpoint d hd
      _ = 2 * ∑ d ∈ Finset.range (N + 1), 1 / (d : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hHarmonic (by norm_num)
  have hTail : |W * (∑ d ∈ Finset.range (N + 1), pd1c_rootEulerCoefficient S d) - W * pd1c_rootEulerConstant S| ≤
      W * (1 / (N : ℝ)) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hW]
    have ht := pd1c_rootEuler_prefix_error S N hS hN
    exact mul_le_mul_of_nonneg_left (by simpa only [abs_sub_comm] using ht) hW
  rw [hReindex]
  have htri := abs_sub_le (∑ d ∈ Finset.range (N + 1), t d)
    (W * ∑ d ∈ Finset.range (N + 1), pd1c_rootEulerCoefficient S d) (W * pd1c_rootEulerConstant S)
  exact htri.trans (add_le_add hFinite hTail)

end ArtinPrimitiveRoots.TypeII.PD
