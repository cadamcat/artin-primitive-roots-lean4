import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.Defs

set_option autoImplicit false
open scoped ContDiff

namespace ArtinPrimitiveRoots.A1.Spec

/-- A nonzero nonnegative smooth bump inside the fixed radial window.
Guide: `sol-thin-spec/PROOFS.md:402`. Uses Mathlib smooth bumps; supplies the
kernel existence conjuncts of the frozen `S1_smoothing`. -/
theorem radialKernel_bump :
    ∃ k₀ : ℝ → ℝ, ContDiff ℝ ∞ k₀ ∧ (∀ t, 0 ≤ k₀ t) ∧
      {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100) ∧ (∃ t, k₀ t ≠ 0) := by
  let b : ContDiffBump (201 / 200 : ℝ) :=
    ⟨1 / 800, 1 / 400, by norm_num, by norm_num⟩
  refine ⟨b, b.contDiff, ?_, ?_, ?_⟩
  · intro t
    exact b.nonneg
  · intro t ht
    change t ∈ Function.support (b : ℝ → ℝ) at ht
    rw [show Function.support b = Metric.ball (201 / 200 : ℝ) (1 / 400) by
      exact b.support_eq] at ht
    have hdist : |t - (201 / 200 : ℝ)| < 1 / 400 := by
      simpa [Real.dist_eq] using (Metric.mem_ball.mp ht)
    constructor
    · have h := (abs_lt.mp hdist).1
      nlinarith
    · have h := (abs_lt.mp hdist).2
      nlinarith
  · refine ⟨201 / 200, ?_⟩
    have hcenter : (201 / 200 : ℝ) ∈ Metric.closedBall (201 / 200 : ℝ) b.rIn := by
      simp [b]
    rw [b.one_of_mem_closedBall hcenter]
    norm_num

end ArtinPrimitiveRoots.A1.Spec
