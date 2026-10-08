import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- The shifted PRODUCT-lattice estimate, uniform in the shift and individual scales.
Guide: `sol-thin-spec/PROOFS.md:353–357,360`. Uses only denominator-lattice discreteness,
product shell packing, and finite products of geometric series; feeds
`balanced_first_coordinate_fiber_bound`. The constant is chosen before the exponent,
shift and scales; the exponent threshold is one, independent of the number of places. -/
theorem shifted_product_lattice_bound (D : ℕ) (hD : 0 < D)
    (lmin αmin αmax : ℝ) (hlmin : 0 < lmin) (hαmin : 1 < αmin)
    (hαrange : αmin ≤ αmax) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, αmin ≤ α → α ≤ αmax →
      ∀ (u : InfinitePlace F → ℂ) (l : InfinitePlace F → ℝ),
        (∀ w, lmin ≤ l w) →
        Summable (fun a : DenominatorScalars (F := F) D =>
          shiftedProductKernel u l α a.1) ∧
        (∑' a : DenominatorScalars (F := F) D, shiftedProductKernel u l α a.1) ≤
          C * ∏ w : InfinitePlace F, Real.rpow (l w) (2 - 2 * α) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
