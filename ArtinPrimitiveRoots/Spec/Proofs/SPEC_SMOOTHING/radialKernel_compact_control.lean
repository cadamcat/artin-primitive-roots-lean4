import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_coord_smooth
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_support_thickening

set_option autoImplicit false
open NumberField
open scoped ContDiff

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- A common positive coordinate neighborhood, compact integration set, and bounds for every
kernel derivative. Nonnegativity and nonvanishing of the kernel are not required.
Guide: `sol-thin-spec/PROOFS.md:402–405`. Uses `radialKernel_coord_smooth`,
`radialKernel_support_thickening` and frozen `G1_h3_basics`; supplies the control hypothesis
of `param_deriv_integral_formula`, hence S1 and S3. -/
theorem radialKernel_compact_control (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F) :
    ∃ (U : Set (Coord F)) (W : Set (X F)),
      IsOpen U ∧ K ⊆ U ∧ U ⊆ posSet F ∧ IsCompact W ∧
        SmoothingKernelControl F k₀ U W := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
