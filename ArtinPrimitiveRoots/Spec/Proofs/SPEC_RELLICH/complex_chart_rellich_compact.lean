import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Recombine supported real H¹ maps into a compact complex-linear chart map.
Guide: runs/lanes/sol-thin-spec/PROOFS.md:320. Uses only the prebuilt Euclidean
isCompactOperator_h1OnToL2 and Mathlib compact-operator composition/addition.
The I compatibility is furnished by localized_chart_extension. -/
theorem complex_chart_rellich_compact
    {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (C : Set (EuclideanSpace ℝ ι)) (hC : IsCompact C)
    (A B : V →L[ℝ] ↥(RellichEuclidean.h1On C hC.measurableSet))
    (hI : ∀ x, A (Complex.I • x) = -B x ∧ B (Complex.I • x) = A x) :
    ∃ L : V →L[ℂ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)),
      IsCompactOperator L ∧
      L.restrictScalars ℝ = rellichRecombine C hC.measurableSet A B := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
