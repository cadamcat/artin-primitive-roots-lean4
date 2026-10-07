import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Extend norm domination from the dense test graph and transfer compactness.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:322-323. Uses e.graph_eq, the estimate
periodization_L2_bound, and the compact chart map complex_chart_rellich_compact.
Factor R through the closure of the range of L by LinearMap.extendOfNorm. -/
theorem rellich_compact_of_test_bound
    (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E)
    (R : E.V →L[ℂ] L2Space F D) (L : E.V →L[ℂ] RellichChartL2 F)
    (hL : IsCompactOperator L) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f : testSubmodule F Γ,
      ‖R (rellichTestVector e f)‖ ≤ C * ‖L (rellichTestVector e f)‖) :
    IsCompactOperator R := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
