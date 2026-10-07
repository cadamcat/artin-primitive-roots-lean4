import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_compact_control
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.param_deriv_integral_formula
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.localLiftCLM

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Smoothing every quotient L2 vector gives a smooth representative in positive coordinates.
Guide: `sol-thin-spec/PROOFS.md:408`. Uses `radialKernel_compact_control`,
`param_deriv_integral_formula`, `localLiftCLM`, and frozen `G3_volume`, `T1_l2`.
Supplies the smoothness conjunct of frozen `S1_smoothing`. -/
theorem smoothing_smooth_representative (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (u : L2Space F D) :
    IsSmoothX F (smoothingOperator F k₀ (l2Lift F Γ D u)) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
