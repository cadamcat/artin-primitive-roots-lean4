import ArtinPrimitiveRoots.TypeII.PD.Memory
import Mathlib.NumberTheory.DiophantineApproximation.Basic

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- The small Fourier shift keeps a minor-arc phase away from all small denominators. -/
theorem pd4c_minor_rational_approximation (x Y A₀ θ u : ℝ)
    (hP : 1 ≤ Real.rpow (Real.log x) A₀)
    (hPY : Real.rpow (Real.log x) A₀ ≤ Y)
    (hminor : ¬ majorArc x Y A₀ θ)
    (hu : |u| ≤ Real.rpow (Real.log x) A₀ / 2) :
    ∃ c : ℤ, ∃ d : ℕ,
      Real.rpow (Real.log x) A₀ < (d : ℝ) ∧
      (d : ℝ) ≤ 2 * Y / Real.rpow (Real.log x) A₀ ∧
      Int.gcd c d = 1 ∧
      |θ + u / Y - (c : ℝ) / (d : ℝ)| ≤ 1 / (d : ℝ) ^ 2 := by
  let P := Real.rpow (Real.log x) A₀
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hP
  have hYpos : 0 < Y := lt_of_lt_of_le hPpos hPY
  have hratio : 1 ≤ Y / P := (le_div_iff₀ hPpos).2 (by simpa only [one_mul] using hPY)
  let n : ℕ := ⌈Y / P⌉₊
  have hnlo : Y / P ≤ (n : ℝ) := Nat.le_ceil _
  have hnhi : (n : ℝ) < Y / P + 1 := Nat.ceil_lt_add_one (by positivity)
  have hnpos : 0 < n := by
    have hnr : 0 < (n : ℝ) := by linarith
    exact_mod_cast hnr
  obtain ⟨q, hq, hqn⟩ := Real.exists_rat_abs_sub_le_and_den_le (θ + u / Y) hnpos
  have hdpos : 0 < (q.den : ℝ) := by exact_mod_cast q.pos
  have hdone : 1 ≤ q.den := Nat.one_le_iff_ne_zero.mpr q.den_nz
  have hdoner : (1 : ℝ) ≤ q.den := by exact_mod_cast hdone
  have hdn : (q.den : ℝ) ≤ n := by exact_mod_cast hqn
  have hqgcd : Int.gcd q.num q.den = 1 := by
    simpa [Int.gcd_def] using q.reduced.gcd_eq_one
  have herror : |θ + u / Y - (q : ℝ)| ≤ 1 / (q.den : ℝ) ^ 2 := by
    calc
      _ ≤ 1 / (((n : ℝ) + 1) * q.den) := by simpa using hq
      _ ≤ 1 / (q.den : ℝ) ^ 2 := by
        apply one_div_le_one_div_of_le (by positivity)
        have h := mul_le_mul_of_nonneg_right (show (q.den : ℝ) ≤ (n : ℝ) + 1 by linarith) hdpos.le
        simpa [pow_two] using h
  have herrorSmall : |θ + u / Y - (q : ℝ)| ≤ P / Y := by
    have hden : Y / P ≤ ((n : ℝ) + 1) * q.den := by
      calc
        _ ≤ (n : ℝ) + 1 := by linarith
        _ ≤ ((n : ℝ) + 1) * q.den := by
          have h := mul_le_mul_of_nonneg_left hdoner (show 0 ≤ (n : ℝ) + 1 by positivity)
          simpa using h
    calc
      _ ≤ 1 / (((n : ℝ) + 1) * q.den) := by simpa using hq
      _ ≤ 1 / (Y / P) := one_div_le_one_div_of_le (div_pos hYpos hPpos) hden
      _ = P / Y := by field_simp
  have hlarge : P < (q.den : ℝ) := by
    by_contra hnot
    have hdsmall : (q.den : ℝ) ≤ P := le_of_not_gt hnot
    have hclose : |θ - (q : ℝ)| ≤ 2 * P / Y := by
      calc
        _ = |(θ + u / Y - (q : ℝ)) - u / Y| := by congr 1; ring
        _ ≤ |θ + u / Y - (q : ℝ)| + |u / Y| := abs_sub _ _
        _ ≤ P / Y + (P / 2) / Y := by
          apply add_le_add herrorSmall
          rw [abs_div, abs_of_pos hYpos]
          exact div_le_div_of_nonneg_right hu hYpos.le
        _ = (3 / 2 : ℝ) * (P / Y) := by ring
        _ ≤ 2 * (P / Y) := mul_le_mul_of_nonneg_right (by norm_num) (div_pos hPpos hYpos).le
        _ = 2 * P / Y := by ring
    apply hminor
    refine ⟨q.num, q.den, hdone, hdsmall, hqgcd, 0, ?_⟩
    simpa [Rat.cast_def, P] using hclose
  refine ⟨q.num, q.den, hlarge, ?_, hqgcd, ?_⟩
  · calc
      (q.den : ℝ) ≤ (n : ℝ) := hdn
      _ ≤ 2 * (Y / P) := by linarith
      _ = 2 * Y / Real.rpow (Real.log x) A₀ := by dsimp [P]; ring
  · simpa [Rat.cast_def] using herror

end

end ArtinPrimitiveRoots.TypeII.PD
