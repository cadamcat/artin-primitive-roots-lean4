import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.Defs

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Isometry equivariance for every radial kernel and function, including the Bochner integral's
nonintegrable case. Guide: `sol-thin-spec/PROOFS.md:407`. Uses frozen `G2_x_action`,
`G3_volume`, `G6_ppi`; supplies the equivariance and invariance conjuncts of `S1_smoothing`. -/
theorem smoothing_isometry_equivariant (k₀ : ℝ → ℝ)
    (g : InfinitePlace F → SL(2,ℂ)) (f : X F → ℂ) (z : X F) :
    smoothingOperator F k₀ (fun x => f (actAtPlaces F g x)) z =
      smoothingOperator F k₀ f (actAtPlaces F g z) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
