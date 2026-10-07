import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Indicator multiplication on the measurable orbit saturation of a compact set.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:317. Uses G1_h3_basics and countability of Γ;
provides the representative and contraction consumed by T6_rellich. -/
theorem orbitRestrictedMass_eq_indicator
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (K : Set (X F)) (hK : IsCompact K) :
    MeasurableSet (orbitSaturation F Γ K) ∧
    ∃ I : L2Space F D →L[ℂ] L2Space F D, RellichIndicator Γ D K I := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
