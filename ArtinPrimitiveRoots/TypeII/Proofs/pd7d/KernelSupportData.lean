import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ScaledDifferenceDerivatives

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

lemma pd7d_scaled_difference_continuous (X : ℝ) : Continuous (pd7dScaledDifference X) := by
  have hfun : pd7dScaledDifference X = fun u => X *
      (Real.exp (pd7dDifferenceLinear X u) - Real.exp (pd7dZLinear u)) := by
    funext u
    exact pd7dScaledDifference_eq X u
  rw [hfun]
  exact continuous_const.mul
    ((Real.continuous_exp.comp (pd7dDifferenceLinear X).continuous).sub
      (Real.continuous_exp.comp pd7dZLinear.continuous))

lemma pd7d_scaled_kernel_tsupport_data (κ ψ : ℝ → ℝ) (X lam R : ℝ)
    (hκ : Function.support κ ⊆ Set.Icc (1 / 2 : ℝ) 32)
    (hψ : Function.support ψ ⊆ Set.Icc (-R) R) (u : PDPlane)
    (hu : u ∈ tsupport (pd7dScaledKernel κ ψ X lam)) :
    |pd7dScaledDifference X u| ≤ R ∧
      Real.exp (pd7dDifferenceLinear X u) ≤ 32 ∧ Real.exp (pd7dZLinear u) ≤ 32 := by
  let S := {u : PDPlane | |pd7dScaledDifference X u| ≤ R ∧
    Real.exp (pd7dDifferenceLinear X u) ≤ 32 ∧ Real.exp (pd7dZLinear u) ≤ 32}
  have hsupp : Function.support (pd7dScaledKernel κ ψ X lam) ⊆ S := by
    intro v hv
    have hκ₀ : κ (Real.exp (v 1)) ≠ 0 := by
      intro hz
      exact hv (by simp [pd7dScaledKernel, hz])
    have hκ₁ : κ (Real.exp (v 1 + v 0 / X)) ≠ 0 := by
      intro hz
      exact hv (by simp [pd7dScaledKernel, hz])
    have hψ₀ : ψ (pd7dScaledDifference X v) ≠ 0 := by
      intro hz
      exact hv (by simp [pd7dScaledKernel, hz])
    exact ⟨abs_le.mpr (hψ hψ₀),
      by simpa only [pd7dDifferenceLinear_apply] using (hκ hκ₁).2,
      by simpa only [pd7dZLinear_apply] using (hκ hκ₀).2⟩
  have hclosed : IsClosed S :=
    (isClosed_le (pd7d_scaled_difference_continuous X).abs continuous_const).inter
      ((isClosed_le (Real.continuous_exp.comp (pd7dDifferenceLinear X).continuous) continuous_const).inter
        (isClosed_le (Real.continuous_exp.comp pd7dZLinear.continuous) continuous_const))
  exact (closure_minimal hsupp hclosed) hu

lemma pd7d_scaled_kernel_support_difference_bound (κ ψ : ℝ → ℝ) (X lam R : ℝ)
    (hX : 1 ≤ X) (hR : 0 ≤ R)
    (hκ : Function.support κ ⊆ Set.Icc (1 / 2 : ℝ) 32)
    (hψ : Function.support ψ ⊆ Set.Icc (-R) R) (u : PDPlane)
    (hu : u ∈ tsupport (pd7dScaledKernel κ ψ X lam)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (pd7dScaledDifference X) u‖ ≤ R + (n : ℝ) * 32 * 2 ^ n := by
  obtain ⟨hg, he, _⟩ := pd7d_scaled_kernel_tsupport_data κ ψ X lam R hκ hψ u hu
  exact pd7d_scaled_difference_derivative_norm_le X R 32 hX hR (by norm_num) u hg he n

end ArtinPrimitiveRoots.TypeII.PD
