import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GAP.CuspSums

/-! L² convergence and graph-closure facts used by `T5_cutoff`. -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

theorem specGapLpTwo_norm_sq_eq_integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (u : Lp E 2 μ) :
    ‖u‖ ^ 2 = ∫ z, ‖u z‖ ^ 2 ∂μ := by
  calc
    ‖u‖ ^ 2 = RCLike.re (inner ℂ u u) := norm_sq_eq_re_inner (𝕜 := ℂ) u
    _ = RCLike.re (∫ z, inner ℂ (u z) (u z) ∂μ) := by rw [L2.inner_def]
    _ = ∫ z, RCLike.re (inner ℂ (u z) (u z)) ∂μ :=
      (integral_re (L2.integrable_inner u u)).symm
    _ = ∫ z, ‖u z‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [inner_self_eq_norm_sq_to_K, pow_two, pow_two]
      change Complex.re ((‖u z‖ : ℂ) * (‖u z‖ : ℂ)) = ‖u z‖ * ‖u z‖
      simp [Complex.mul_re]

theorem specGapLpTwo_integrable_norm_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (u : Lp E 2 μ) : Integrable (fun z => ‖u z‖ ^ 2) μ := by
  simpa using (Lp.memLp u).integrable_norm_rpow (by norm_num) (by norm_num)

theorem specGapLpTwo_tendsto_zero {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (seq : ℕ → Lp E 2 μ)
    (hInt : Tendsto (fun n => ∫ z, ‖seq n z‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto seq atTop (𝓝 0) := by
  have hnormSqEq (n : ℕ) : ‖seq n‖ ^ 2 = ∫ z, ‖seq n z‖ ^ 2 ∂μ :=
    specGapLpTwo_norm_sq_eq_integral μ (seq n)
  have hnormSq : Tendsto (fun n => ‖seq n‖ ^ 2) atTop (𝓝 0) := by
    simpa only [← hnormSqEq] using hInt
  have hsqrt : Tendsto (fun n => Real.sqrt (‖seq n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hnormSq
  have hnorm : Tendsto (fun n => ‖seq n‖) atTop (𝓝 0) := by
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt
  exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm

theorem specGap_energyGraph_limit {T H G : Type*}
    [AddCommGroup T] [Module ℂ T]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (toL2 : T →ₗ[ℂ] H) (gradL2 : T →ₗ[ℂ] G)
    (seq : ℕ → T) (u : H) (v : G)
    (hlim : Tendsto (fun n => energyGraphMap toL2 gradL2 (seq n)) atTop
      (𝓝 (WithLp.toLp 2 (u, v)))) :
    WithLp.toLp 2 (u, v) ∈ energyGraph toL2 gradL2 := by
  change WithLp.toLp 2 (u, v) ∈ closure (energyGraphMap toL2 gradL2).range
  apply (isClosed_closure : IsClosed (closure (energyGraphMap toL2 gradL2).range)).mem_of_tendsto hlim
  filter_upwards [] with n
  exact subset_closure ⟨seq n, rfl⟩

end ArtinPrimitiveRoots.A1.Spec

end
