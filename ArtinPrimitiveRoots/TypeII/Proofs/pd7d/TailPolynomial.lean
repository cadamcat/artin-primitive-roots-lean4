import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

lemma pd7d_complex_phase_norm (u v : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ) * (v : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
    zero_sub, sub_zero, add_zero, zero_add, Real.exp_zero]

noncomputable def pd7dTailPolynomial {α : Type*} (Rset : Finset α) (b : α → ℕ)
    (W P Y : ℝ) (chi : ℕ → ℂ) (t : ℝ) : ℂ :=
  (P / Y : ℂ) * ∑ r ∈ Rset.filter (fun r =>
      Y / (2 * P) ≤ (b r : ℝ) ∧ (b r : ℝ) ≤ 4 * Y / P),
    (W : ℂ) * chi (b r) * Complex.exp (Complex.I * t * Real.log (b r : ℝ))

lemma pd7dTailPolynomial_norm_le {α : Type*} (Rset : Finset α) (b : α → ℕ)
    (W P Y : ℝ) (chi : ℕ → ℂ) (t : ℝ)
    (hW : 0 ≤ W) (hP : 0 < P) (hY : 0 < Y)
    (hb : ∀ r ∈ Rset, 0 < b r) (hchi : ∀ r ∈ Rset, ‖chi (b r)‖ ≤ 1) :
    ‖pd7dTailPolynomial Rset b W P Y chi t‖ ≤ 4 * ∑ r ∈ Rset, W / (b r : ℝ) := by
  let S := Rset.filter (fun r => Y / (2 * P) ≤ (b r : ℝ) ∧ (b r : ℝ) ≤ 4 * Y / P)
  have hscale : ‖(P / Y : ℂ)‖ = P / Y := by
    rw [norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hP, abs_of_pos hY]
  have hterm (r : α) (hr : r ∈ S) :
      ‖(W : ℂ) * chi (b r) * Complex.exp (Complex.I * t * Real.log (b r : ℝ))‖ ≤ W := by
    have hmem : r ∈ Rset := (Finset.mem_filter.mp hr).1
    have hphase : ‖Complex.exp (Complex.I * t * Real.log (b r : ℝ))‖ = 1 := pd7d_complex_phase_norm t (Real.log (b r : ℝ))
    rw [norm_mul, norm_mul, hphase, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hW]
    simpa using mul_le_mul_of_nonneg_left (hchi r hmem) hW
  have hcomp (r : α) (hr : r ∈ S) : P / Y * W ≤ 4 * (W / (b r : ℝ)) := by
    have hr' := Finset.mem_filter.mp hr
    have hbr : 0 < (b r : ℝ) := by exact_mod_cast hb r hr'.1
    have hPb : P * (b r : ℝ) ≤ 4 * Y := by
      have hh := (le_div_iff₀ hP).mp hr'.2.2
      nlinarith
    have hratio : P / Y ≤ 4 / (b r : ℝ) := (div_le_div_iff₀ hY hbr).2 hPb
    calc
      _ ≤ 4 / (b r : ℝ) * W := mul_le_mul_of_nonneg_right hratio hW
      _ = _ := by ring
  calc
    _ = (P / Y) * ‖∑ r ∈ S,
        (W : ℂ) * chi (b r) * Complex.exp (Complex.I * t * Real.log (b r : ℝ))‖ := by
      rw [pd7dTailPolynomial, norm_mul, hscale]
    _ ≤ (P / Y) * ∑ r ∈ S, W := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = ∑ r ∈ S, P / Y * W := Finset.mul_sum _ _ _
    _ ≤ ∑ r ∈ S, 4 * (W / (b r : ℝ)) := Finset.sum_le_sum hcomp
    _ ≤ ∑ r ∈ Rset, 4 * (W / (b r : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro r hr _
      positivity
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma pd7d_normalized_polynomial_norm_le (H : ℝ) (S : Finset ℕ) (c : ℕ → ℂ)
    (t : ℝ) (hH : 0 < H) :
    ‖(1 / H : ℂ) * ∑ n ∈ S, c n * Complex.exp (Complex.I * t * Real.log (n : ℝ))‖ ≤
      (∑ n ∈ S, ‖c n‖) / H := by
  have hscale : ‖(1 / H : ℂ)‖ = 1 / H := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  rw [norm_mul, hscale]
  calc
    _ ≤ (1 / H) * ∑ n ∈ S, ‖c n * Complex.exp (Complex.I * t * Real.log (n : ℝ))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = _ := by
      simp only [norm_mul, pd7d_complex_phase_norm, mul_one]
      ring

end ArtinPrimitiveRoots.TypeII.PD
