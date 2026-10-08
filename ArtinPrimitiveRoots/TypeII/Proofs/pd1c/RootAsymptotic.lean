import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootGraph

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
set_option maxHeartbeats 1000000

lemma pd1c_root_modulus_small (δ C_K : ℝ) (hδ : 0 < δ) (hCK : 0 < C_K) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ S : ℝ,
      S ≤ Real.exp (C_K * (Real.log x) ^ (98 / 100 : ℝ)) → S ≤ x ^ (δ / 1000) := by
  have he : ∀ᶠ L : ℝ in atTop, L ^ (-(1 / 50 : ℝ)) ≤ δ / (1000 * C_K) :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 50)).eventually
      (Iio_mem_nhds (by positivity))).mono (fun L h => h.le)
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp he
  let L₀ := max 1 L₁
  refine ⟨max 2 (Real.exp L₀), le_max_left _ _, ?_⟩
  intro x hx S hS
  have hLp : L₀ ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos L₀) ((le_max_right _ _).trans hx)
  have hL : 0 < Real.log x := lt_of_lt_of_le (by dsimp [L₀]; positivity) hLp
  have hxpos : 0 < x := by linarith [(le_max_left 2 (Real.exp L₀)).trans hx]
  have h := hL₁ (Real.log x) ((le_max_right _ _).trans hLp)
  have hmul : C_K * (Real.log x) ^ (-(1 / 50 : ℝ)) ≤ δ / 1000 := by
    have hm := (le_div_iff₀ (by positivity : 0 < 1000 * C_K)).mp h
    nlinarith
  have hPow : (Real.log x) ^ (98 / 100 : ℝ) = Real.log x * (Real.log x) ^ (-(1 / 50 : ℝ)) := by
    calc
      _ = (Real.log x) ^ (1 + -(1 / 50 : ℝ)) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hL, Real.rpow_one]
  calc
    _ ≤ Real.exp (C_K * (Real.log x) ^ (98 / 100 : ℝ)) := hS
    _ ≤ Real.exp (Real.log x * (δ / 1000)) := Real.exp_le_exp.mpr (by
      rw [hPow]
      nlinarith [mul_le_mul_of_nonneg_right hmul hL.le])
    _ = _ := (Real.rpow_def_of_pos hxpos _).symm

lemma pd1c_root_log_error (W : ℝ) (hW : 1 ≤ W) :
    Real.log (2 * W) / W ≤ 4 * W ^ (-(1 / 2 : ℝ)) := by
  have hWp : 0 < W := lt_of_lt_of_le (by norm_num) hW
  have hlog := Real.log_le_rpow_div (x := 2 * W) (by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
  have hpow2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have htop : (2 * W) ^ (1 / 2 : ℝ) ≤ 2 * W ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hWp.le]
    exact mul_le_mul_of_nonneg_right hpow2 (Real.rpow_nonneg hWp.le _)
  have hExp : W ^ (1 / 2 : ℝ) / W = W ^ (-(1 / 2 : ℝ)) := by
    calc
      W ^ (1 / 2 : ℝ) / W = W ^ (1 / 2 : ℝ) / W ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = W ^ ((1 / 2 : ℝ) - 1) := (Real.rpow_sub hWp _ _).symm
      _ = _ := by congr 1; norm_num
  calc
    _ ≤ ((2 * W) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) / W := div_le_div_of_nonneg_right hlog hWp.le
    _ ≤ (4 * W ^ (1 / 2 : ℝ)) / W := by
      apply div_le_div_of_nonneg_right _ hWp.le
      nlinarith [htop]
    _ = 4 * (W ^ (1 / 2 : ℝ) / W) := by ring
    _ = _ := by rw [hExp]

lemma pd1c_root_error_absorb (δ C_K : ℝ) (hδ : 0 < δ) (hCK : 0 < C_K) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ W S : ℝ,
      x ^ δ ≤ W → 0 ≤ S → S ≤ Real.exp (C_K * (Real.log x) ^ (98 / 100 : ℝ)) →
      W ^ (-(1 / 100 : ℝ)) * S ^ 2 + Real.log (2 * W) / W + W ^ (-2 : ℝ) ≤
        6 * x ^ (-(δ / 1000)) := by
  obtain ⟨x₀, hx₀, hMod⟩ := pd1c_root_modulus_small δ C_K hδ hCK
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx W S hW hS₀ hS
  have hx1 : 1 ≤ x := by linarith [hx₀.trans hx]
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx1
  have hxδ : 1 ≤ x ^ δ := Real.one_le_rpow hx1 hδ.le
  have hW1 : 1 ≤ W := hxδ.trans hW
  have hWp : 0 < W := lt_of_lt_of_le (by norm_num) hW1
  have hModSmall := hMod x hx S hS
  have hRpow : ∀ e : ℝ, e ≤ 0 → W ^ e ≤ x ^ (δ * e) := by
    intro e he
    calc
      _ ≤ (x ^ δ) ^ e := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hxpos _) hW he
      _ = _ := (Real.rpow_mul hxpos.le _ _).symm
  have hFirst : W ^ (-(1 / 100 : ℝ)) * S ^ 2 ≤ x ^ (-(δ / 1000)) := by
    calc
      _ ≤ x ^ (δ * -(1 / 100 : ℝ)) * (x ^ (δ / 1000)) ^ 2 :=
        mul_le_mul (hRpow _ (by norm_num)) (pow_le_pow_left₀ hS₀ hModSmall 2) (sq_nonneg _) (by positivity)
      _ = x ^ (-(δ / 125)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le, ← Real.rpow_add hxpos]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hSecond : Real.log (2 * W) / W ≤ 4 * x ^ (-(δ / 1000)) := by
    calc
      _ ≤ 4 * W ^ (-(1 / 2 : ℝ)) := pd1c_root_log_error W hW1
      _ ≤ 4 * x ^ (δ * -(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left (hRpow _ (by norm_num)) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) (by norm_num)
  have hThird : W ^ (-2 : ℝ) ≤ x ^ (-(δ / 1000)) :=
    (hRpow _ (by norm_num)).trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  linarith

end ArtinPrimitiveRoots.TypeII.PD
