import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Uniform H¹ estimates for a calibrated real/imaginary cutoff test localization.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:318. Uses the local-energy bound from
quotient_to_chart_finite_overlap, compact bounds on heights/density/cutoff derivatives,
and the mass and gradient representatives of localized_chart_H1_membership. -/
theorem localized_chart_H1_bound
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (htests : ∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f)
    (hlocal : RellichLocalEnergyBound Γ D E e)
    (ψ : X F → ℝ) (hψsmooth : IsSmoothRealX F ψ)
    (hψcompact : HasCompactSupportX F (fun z => (ψ z : ℂ)))
    (c : RellichTestChart Γ ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : testSubmodule F Γ,
      ‖c.re f‖ ≤ C * (‖e.toL2 f‖ + ‖e.gradL2 f‖) ∧
      ‖c.im f‖ ≤ C * (‖e.toL2 f‖ + ‖e.gradL2 f‖) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
