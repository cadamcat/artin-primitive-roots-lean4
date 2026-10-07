import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_compact_control

set_option autoImplicit false
open NumberField MeasureTheory
open scoped ContDiff

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Representatives equal a.e. on each compact set have equal smoothing at every point.
Guide: `sol-thin-spec/PROOFS.md:409`. Uses `radialKernel_compact_control` and frozen
`G1_h3_basics`; provides the stronger representative-independence needed by S3.
No integrability hypothesis is needed for equality of the Bochner integrals. -/
theorem smoothing_representative_independent (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (f f' : X F → ℂ)
    (hff' : ∀ W : Set (X F), IsCompact W →
      ∀ᵐ z ∂(volX F), z ∈ W → f z = f' z) (z : X F) :
    smoothingOperator F k₀ f z = smoothingOperator F k₀ f' z := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
