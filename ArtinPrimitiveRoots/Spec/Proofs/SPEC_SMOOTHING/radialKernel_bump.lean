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
  sorry

end ArtinPrimitiveRoots.A1.Spec
