import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- The cutoff test has supported real and imaginary H¹ representatives after zero extension.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:318-319. Uses G1_h3_basics, G2_x_action and the
T2 test characterization; the compact cutoff vanishes near the positive-chart boundary.
Build C1c representatives and their core maps into h1On, including gradient calibration. -/
theorem localized_chart_H1_membership
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (htests : ∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f)
    (ψ : X F → ℝ) (hψsmooth : IsSmoothRealX F ψ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ))) :
    Nonempty (RellichTestChart Γ ψ) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
