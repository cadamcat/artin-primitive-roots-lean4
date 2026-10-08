import ArtinPrimitiveRoots.TypeII.PD.Preliminaries

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical

/-- The frozen divisor moment input is uniform at every Type II product scale. -/
theorem tau_secondMoment_scale_bound (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ κ Ct x₀ : ℝ, 0 < κ ∧ 0 < Ct ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ X : ℝ, c₁ * x ≤ X → X ≤ c₂ * x →
        (∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), (tau n : ℝ) ^ 2) ≤
          Ct * X * Real.rpow (Real.log x) κ := by
  obtain ⟨κ, hκ, Y₀, hY₀, hmoment⟩ := moment_bounds.1 2
  let Ct := 4 * κ * Real.rpow 2 κ
  let x₀ := max 2 (max (Real.exp 1) (max (Real.exp |Real.log (8 * c₂)|) (Y₀ / (4 * c₁))))
  refine ⟨κ, Ct, x₀, hκ, by dsimp [Ct]; positivity, by simp [x₀], ?_⟩
  intro x hx X hXlo hXhi
  have hx₂ : 2 ≤ x := (by simp [x₀] : 2 ≤ x₀).trans hx
  have hxpos : 0 < x := by linarith
  have hXpos : 0 < X := (mul_pos hc₁ hxpos).trans_le hXlo
  have hY : Y₀ ≤ 4 * X := by
    have hd : Y₀ / (4 * c₁) ≤ x := (by simp [x₀] : Y₀ / (4 * c₁) ≤ x₀).trans hx
    have ht := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hc₁)).mp hd
    nlinarith
  have hLone : 1 ≤ Real.log x := by
    have he : Real.exp 1 ≤ x := (by simp [x₀] : Real.exp 1 ≤ x₀).trans hx
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) he
  have hCLog : Real.log (8 * c₂) ≤ Real.log x := by
    have he : Real.exp |Real.log (8 * c₂)| ≤ x :=
      (by simp [x₀] : Real.exp |Real.log (8 * c₂)| ≤ x₀).trans hx
    have hl := Real.log_le_log (Real.exp_pos _) he
    rw [Real.log_exp] at hl
    exact (le_abs_self _).trans hl
  have hlog : Real.log (8 * X) ≤ 2 * Real.log x := by
    have hi : 8 * X ≤ (8 * c₂) * x := by nlinarith
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < 8 * X) hi
    rw [Real.log_mul (by positivity : (8 * c₂ : ℝ) ≠ 0) hxpos.ne'] at hl
    linarith
  have hlog0 : 0 ≤ Real.log (8 * X) := Real.log_nonneg (by linarith [hY₀])
  have hp := Real.rpow_le_rpow hlog0 hlog hκ.le
  have hpow : Real.rpow (2 * Real.log x) κ = Real.rpow 2 κ * Real.rpow (Real.log x) κ :=
    Real.mul_rpow (by norm_num) (by linarith [hLone])
  have hm := (hmoment (4 * X) hY).1
  have heq : 2 * (4 * X) = 8 * X := by ring
  rw [heq] at hm
  calc
    _ ≤ κ * (4 * X) * Real.rpow (Real.log (8 * X)) κ := hm
    _ ≤ κ * (4 * X) * Real.rpow (2 * Real.log x) κ :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [hpow]; dsimp [Ct]; ring

end ArtinPrimitiveRoots.TypeII.PD
