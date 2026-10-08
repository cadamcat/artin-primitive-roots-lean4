import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.FrequencyWeights

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option autoImplicit false

lemma pd7d_separation_log_bound (L A₀ B₀ B₁ A' C₄ D CQ Z : ℝ) (j : ℕ)
    (hL : 1 ≤ L) (hCQ : 0 ≤ CQ)
    (hret : 9*A₀+B₁-A' ≤ -D)
    (htail : 9*A₀+C₄+B₀+B₁+(j : ℝ)*(B₀-B₁) ≤ -D) :
    (Real.rpow L A₀)^9 *
      (2*Real.rpow L B₁*Real.rpow L (-A') +
        32*(CQ*Real.rpow L C₄)*Real.rpow L B₀*Real.rpow L B₁*
          (Real.rpow L B₀/Real.rpow L B₁)^j*Z^2) ≤
      (2+32*CQ*Z^2)*Real.rpow L (-D) := by
  have hLp : 0 < L := by linarith
  have hAdd (u v : ℝ) : Real.rpow L u*Real.rpow L v = Real.rpow L (u+v) := (Real.rpow_add hLp u v).symm
  have hMpow : (Real.rpow L A₀)^9 = Real.rpow L (9*A₀) := by
    calc
      _ = Real.rpow (Real.rpow L A₀) (9 : ℝ) := (Real.rpow_natCast _ 9).symm
      _ = Real.rpow L (A₀*9) := (Real.rpow_mul hLp.le _ _).symm
      _ = _ := by congr 1; ring
  have hretEq : (Real.rpow L A₀)^9*Real.rpow L B₁*Real.rpow L (-A') =
      Real.rpow L (9*A₀+B₁-A') := by
    rw [hMpow, hAdd, hAdd]
    congr 1 <;> ring
  have hquot : Real.rpow L B₀/Real.rpow L B₁ = Real.rpow L (B₀-B₁) := (Real.rpow_sub hLp _ _).symm
  have htailEq : (Real.rpow L A₀)^9*Real.rpow L C₄*Real.rpow L B₀*Real.rpow L B₁*
      (Real.rpow L B₀/Real.rpow L B₁)^j =
        Real.rpow L (9*A₀+C₄+B₀+B₁+(j : ℝ)*(B₀-B₁)) := by
    have hjpow : (Real.rpow L (B₀-B₁))^j = Real.rpow L ((B₀-B₁)*(j : ℝ)) := by
      calc
        _ = Real.rpow (Real.rpow L (B₀-B₁)) (j : ℝ) := (Real.rpow_natCast _ j).symm
        _ = _ := (Real.rpow_mul hLp.le _ _).symm
    rw [hMpow,hquot,hjpow]
    repeat rw [hAdd]
    congr 1 <;> ring
  have hr := Real.rpow_le_rpow_of_exponent_le hL hret
  have ht := Real.rpow_le_rpow_of_exponent_le hL htail
  calc
    _ = 2*((Real.rpow L A₀)^9*Real.rpow L B₁*Real.rpow L (-A')) +
      (32*CQ*Z^2)*((Real.rpow L A₀)^9*Real.rpow L C₄*Real.rpow L B₀*Real.rpow L B₁*
        (Real.rpow L B₀/Real.rpow L B₁)^j) := by ring
    _ = 2*Real.rpow L (9*A₀+B₁-A') +
      (32*CQ*Z^2)*Real.rpow L (9*A₀+C₄+B₀+B₁+(j : ℝ)*(B₀-B₁)) := by rw [hretEq,htailEq]
    _ ≤ 2*Real.rpow L (-D)+(32*CQ*Z^2)*Real.rpow L (-D) := add_le_add
      (mul_le_mul_of_nonneg_left hr (by norm_num))
      (mul_le_mul_of_nonneg_left ht (by positivity))
    _ = _ := by ring
end ArtinPrimitiveRoots.TypeII.PD
