import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.PartialDerivativeNorms

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
set_option autoImplicit false

noncomputable def pd7dKernelRadius (R : ℝ) : ℝ :=
  2 * R + |Real.log (1 / 2 : ℝ)| + |Real.log 32|

lemma pd7d_scaled_kernel_tsupport_ball (κ ψ : ℝ → ℝ) (X lam R : ℝ) (hX : 1 ≤ X)
    (hκ : Function.support κ ⊆ Set.Icc (1 / 2 : ℝ) 32)
    (hψ : Function.support ψ ⊆ Set.Icc (-R) R) :
    tsupport (pd7dScaledKernel κ ψ X lam) ⊆ Metric.closedBall (0 : PDPlane) (pd7dKernelRadius R) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro u hu
  obtain ⟨hζ, hz⟩ := pd7d_scaled_kernel_support_box κ ψ X lam R hX hκ hψ u hu
  have hzAbs : |u 1| ≤ |Real.log (1 / 2 : ℝ)| + |Real.log 32| := by
    apply abs_le.mpr
    constructor
    · linarith [hz.1, neg_abs_le (Real.log (1 / 2 : ℝ)), abs_nonneg (Real.log 32)]
    · linarith [hz.2, le_abs_self (Real.log 32), abs_nonneg (Real.log (1 / 2 : ℝ))]
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pd7d_plane_norm_le u).trans (by dsimp [pd7dKernelRadius]; linarith)

lemma pd7d_kernel_dominated_derivative_mass (κ ψ : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hκ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hκsupp : Function.support κ ⊆ Set.Icc (1 / 2 : ℝ) 32)
    (hψsupp : Function.support ψ ⊆ Set.Icc (-R) R) (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ X lam : ℝ, 1 ≤ X → ∀ G : PDPlane → ℂ,
      Integrable G → (∀ u, ‖G u‖ ≤ ‖iteratedFDeriv ℝ n (pd7dScaledKernel κ ψ X lam) u‖) →
      (∫ u : PDPlane, ‖G u‖) ≤ Cn * (1 + |lam|) ^ n := by
  obtain ⟨C, hC, hbound⟩ := pd7d_scaled_kernel_derivative_bound κ ψ R hR hκ hψ hκsupp hψsupp n
  let S := Metric.closedBall (0 : PDPlane) (pd7dKernelRadius R)
  let V := volume.real S
  let Cn := C * V + 1
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hCn : 0 < Cn := by dsimp [Cn]; positivity
  refine ⟨Cn, hCn, ?_⟩
  intro X lam hX G hG hdom
  have hsupp : Function.support G ⊆ S := by
    intro u hu
    have hGpos : 0 < ‖G u‖ := norm_pos_iff.mpr hu
    have hDpos : 0 < ‖iteratedFDeriv ℝ n (pd7dScaledKernel κ ψ X lam) u‖ := hGpos.trans_le (hdom u)
    have hDne := norm_pos_iff.mp hDpos
    have hmem := (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := pd7dScaledKernel κ ψ X lam) n) hDne
    exact pd7d_scaled_kernel_tsupport_ball κ ψ X lam R hX hκsupp hψsupp hmem
  have hpoint : ∀ u, ‖G u‖ ≤ C * (1 + |lam|) ^ n :=
    fun u => (hdom u).trans (hbound X lam hX u)
  have hmass := pd7d_norm_integral_bound_of_support G (C * (1 + |lam|) ^ n)
    (by exact Metric.isClosed_closedBall.measurableSet)
    (by exact (isCompact_closedBall (0 : PDPlane) (pd7dKernelRadius R)).measure_ne_top)
    hG (by positivity) hpoint hsupp
  calc
    _ ≤ C * (1 + |lam|) ^ n * V := hmass
    _ = (C * V) * (1 + |lam|) ^ n := by ring
    _ ≤ Cn * (1 + |lam|) ^ n := mul_le_mul_of_nonneg_right
      (by dsimp [Cn]; linarith) (pow_nonneg (by positivity) n)

end ArtinPrimitiveRoots.TypeII.PD
