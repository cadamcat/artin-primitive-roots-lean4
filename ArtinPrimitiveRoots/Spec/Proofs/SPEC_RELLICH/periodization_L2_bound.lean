import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Periodization and cutoff reconstruction give mass domination by the chart L² norm.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:321-322. Uses T1 compact overlaps and
unfolding, T2's locally finite partition, G3_volume, and calibrated test representatives.
Cauchy-Schwarz gives the finite-overlap bound; positive compact chart density compares
Lebesgue and hyperbolic norms. Only this norm estimate is needed by the compact assembly. -/
theorem periodization_L2_bound
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (htests : ∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f)
    (hOverlap : RellichOverlapControl Γ D) (hUnfold : RellichUnfolding Γ D)
    (K : Set (X F)) (hK : IsCompact K)
    (ψ : X F → ℝ) (hψ : RellichPartition Γ K ψ)
    (I : L2Space F D →L[ℂ] L2Space F D) (hI : RellichIndicator Γ D K I)
    (L : E.V →L[ℂ] RellichChartL2 F)
    (hLrep : ∀ f : testSubmodule F Γ, ∀ᵐ p ∂(volume : Measure (RellichCoord F)),
      L (rellichTestVector e f) p = rellichLocalized F ψ (f : X F → ℂ) p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : testSubmodule F Γ,
      ‖I (e.toL2 f)‖ ≤ C * ‖L (rellichTestVector e f)‖ := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
