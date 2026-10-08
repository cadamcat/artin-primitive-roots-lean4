import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

lemma pd7d_one_add_pow_le_max (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    (1 + r) ^ n ≤ (2 : ℝ) ^ n * max 1 (r ^ n) := by
  by_cases hsmall : r ≤ 1
  · calc
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (le_max_left (1 : ℝ) (r ^ n)) (pow_nonneg (by norm_num) n)
  · have hlarge : 1 ≤ r := le_of_lt (lt_of_not_ge hsmall)
    calc
      _ ≤ (2 * r) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = (2 : ℝ) ^ n * r ^ n := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) (r ^ n)) (pow_nonneg (by norm_num) n)

lemma pd7d_four_weight_envelope (r₀ r₁ s D : ℝ) (n : ℕ)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (hs : 0 ≤ s) (hD : 0 ≤ D)
    (hbase : s ≤ D) (h₀ : r₀ ^ n * s ≤ D) (h₁ : r₁ ^ n * s ≤ D)
    (h₀₁ : r₀ ^ n * r₁ ^ n * s ≤ D) :
    (1 + r₀) ^ n * (1 + r₁) ^ n * s ≤ (4 : ℝ) ^ n * D := by
  let A := max 1 (r₀ ^ n)
  let B := max 1 (r₁ ^ n)
  have hA : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hB : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hAB : A * B * s ≤ D := by
    by_cases hsmall₀ : r₀ ^ n ≤ 1
    · by_cases hsmall₁ : r₁ ^ n ≤ 1
      · simpa only [A, B, max_eq_left hsmall₀, max_eq_left hsmall₁, one_mul] using hbase
      · simpa only [A, B, max_eq_left hsmall₀, max_eq_right (le_of_lt (lt_of_not_ge hsmall₁)), one_mul] using h₁
    · by_cases hsmall₁ : r₁ ^ n ≤ 1
      · simpa only [A, B, max_eq_right (le_of_lt (lt_of_not_ge hsmall₀)), max_eq_left hsmall₁, mul_one] using h₀
      · simpa only [A, B, max_eq_right (le_of_lt (lt_of_not_ge hsmall₀)),
          max_eq_right (le_of_lt (lt_of_not_ge hsmall₁))] using h₀₁
  have hfirst := pd7d_one_add_pow_le_max r₀ hr₀ n
  have hsecond := pd7d_one_add_pow_le_max r₁ hr₁ n
  calc
    _ ≤ ((2 : ℝ) ^ n * A) * ((2 : ℝ) ^ n * B) * s :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hfirst hsecond (pow_nonneg (by linarith) n) (mul_nonneg (pow_nonneg (by norm_num) n) hA)) hs
    _ = (4 : ℝ) ^ n * (A * B * s) := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hAB (pow_nonneg (by norm_num) n)

lemma pd7d_inverse_nat_rpow (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    Real.rpow r (-(n : ℝ)) = (r ^ n)⁻¹ := by
  calc
    _ = (Real.rpow r (n : ℝ))⁻¹ := Real.rpow_neg hr _
    _ = _ := congrArg Inv.inv (Real.rpow_natCast r n)

lemma pd7d_four_weight_decay (r₀ r₁ s D : ℝ) (n : ℕ)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (hs : 0 ≤ s) (hD : 0 ≤ D)
    (hbase : s ≤ D) (h₀ : r₀ ^ n * s ≤ D) (h₁ : r₁ ^ n * s ≤ D)
    (h₀₁ : r₀ ^ n * r₁ ^ n * s ≤ D) :
    s ≤ (4 : ℝ) ^ n * D * Real.rpow (1 + r₀) (-(n : ℝ)) * Real.rpow (1 + r₁) (-(n : ℝ)) := by
  have hp₀ : 0 < 1 + r₀ := by linarith
  have hp₁ : 0 < 1 + r₁ := by linarith
  have henv := pd7d_four_weight_envelope r₀ r₁ s D n hr₀ hr₁ hs hD hbase h₀ h₁ h₀₁
  rw [pd7d_inverse_nat_rpow _ hp₀.le, pd7d_inverse_nat_rpow _ hp₁.le]
  have hden : 0 < (1 + r₀) ^ n * (1 + r₁) ^ n := mul_pos (pow_pos hp₀ n) (pow_pos hp₁ n)
  have hquot : s ≤ ((4 : ℝ) ^ n * D) / ((1 + r₀) ^ n * (1 + r₁) ^ n) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using henv)
  simpa only [div_eq_mul_inv, mul_inv, mul_assoc] using hquot

lemma pd7d_normalize_weight (a s D H : ℝ) (n : ℕ) (hH : 0 < H)
    (hbound : a ^ n * s ≤ D * H ^ n) : (a / H) ^ n * s ≤ D := by
  have hHp : 0 < H ^ n := pow_pos hH n
  calc
    _ = (a ^ n * s) / H ^ n := by rw [div_pow]; ring
    _ ≤ (D * H ^ n) / H ^ n := div_le_div_of_nonneg_right hbound hHp.le
    _ = D := by field_simp

lemma pd7d_normalize_mixed_weight (a b s D H : ℝ) (n : ℕ) (hH : 0 < H)
    (hbound : a ^ n * b ^ n * s ≤ D * H ^ (2 * n)) :
    (a / H) ^ n * (b / H) ^ n * s ≤ D := by
  have hHp : 0 < H ^ (2 * n) := pow_pos hH _
  have hpow : H ^ (2 * n) = H ^ n * H ^ n := by
    rw [show 2 * n = n + n by omega, pow_add]
  calc
    _ = (a ^ n * b ^ n * s) / H ^ (2 * n) := by rw [div_pow, div_pow, hpow]; ring
    _ ≤ (D * H ^ (2 * n)) / H ^ (2 * n) := div_le_div_of_nonneg_right hbound hHp.le
    _ = D := by field_simp

end ArtinPrimitiveRoots.TypeII.PD
