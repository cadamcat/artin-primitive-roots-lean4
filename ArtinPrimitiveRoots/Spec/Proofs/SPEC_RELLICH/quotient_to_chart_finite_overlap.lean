import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Local mass and gradient energy are controlled by calibrated quotient energy.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:319. Uses the compact-overlap conjunct
of T1_l2 (passed as hOverlap), G3_volume, G4_energy and the T2 test characterization.
No freeness or finiteness assertion about translates meeting an unbounded D is used. -/
theorem quotient_to_chart_finite_overlap
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (htests : ∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f)
    (hOverlap : RellichOverlapControl Γ D) :
    RellichLocalEnergyBound Γ D E e := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
