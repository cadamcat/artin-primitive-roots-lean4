import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.Defs

set_option autoImplicit false
open NumberField MeasureTheory
open scoped ContDiff

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Local L1 and compact kernel control give smoothness and all multilinear
derivative-integral identities. Only the representative on W needs to be integrable.
Guide: `sol-thin-spec/PROOFS.md:403–405`. Uses `SmoothingKernelControl` and Mathlib's
`hasFDerivAt_integral_of_dominated_of_fderiv_le`; supplies
`smoothing_uniform_eval_bound`, `smoothing_smooth_representative`, S1 and generic S3 smoothing. -/
theorem param_deriv_integral_formula (k₀ : ℝ → ℝ)
    (U : Set (Coord F)) (hU : IsOpen U) (hUpos : U ⊆ posSet F)
    (W : Set (X F)) (hW : IsCompact W) (hcontrol : SmoothingKernelControl F k₀ U W)
    (f : X F → ℂ) (hfMeas : AEStronglyMeasurable f (volX F))
    (hfInt : IntegrableOn f W (volX F)) :
    ContDiffOn ℝ ∞ (fun q => smoothingOperator F k₀ f (ptX F q)) U ∧
      ∀ (n : ℕ) (p : Coord F), p ∈ U →
        Integrable (fun w => f w •
          iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p) (volX F) ∧
        iteratedFDeriv ℝ n (fun q => smoothingOperator F k₀ f (ptX F q)) p =
          ∫ w, f w • iteratedFDeriv ℝ n
            (fun q => radialKernel F k₀ (ptX F q) w) p ∂(volX F) ∧
        ∀ v : Fin n → Coord F,
          iteratedFDeriv ℝ n (fun q => smoothingOperator F k₀ f (ptX F q)) p v =
            ∫ w, iteratedFDeriv ℝ n
              (fun q => radialKernel F k₀ (ptX F q) w) p v * f w ∂(volX F) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
