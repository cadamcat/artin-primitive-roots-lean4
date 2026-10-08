import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.Defs

set_option autoImplicit false
open NumberField
open scoped ContDiff

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Joint smoothness of the product radial kernel in positive coordinate charts.
Guide: `sol-thin-spec/PROOFS.md:402`. Uses frozen `G1_h3_basics`, `G6_ppi` and the
finite product rule; supplies `radialKernel_compact_control`. -/
theorem radialKernel_coord_smooth (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀) :
    ContDiffOn ℝ ∞
      (fun pq : Coord F × Coord F => radialKernel F k₀ (ptX F pq.1) (ptX F pq.2))
      {pq | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F} := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
