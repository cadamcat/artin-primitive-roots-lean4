import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.shifted_product_lattice_bound

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Substitute `l_w = |w(c)| y_w` in the shifted product-lattice bound.
Balanced nonzero c and positive balanced heights with a product floor give a uniform
positive scale floor. Guide: `sol-thin-spec/PROOFS.md:353–358`. Uses
`shifted_product_lattice_bound` and the positive integer norm lower bound; feeds
`balanced_denominator_rows_bound`. -/
theorem balanced_first_coordinate_fiber_bound (D : ℕ) (hD : 0 < D)
    (Bc By H αmin αmax : ℝ) (hBc : 0 ≤ Bc) (hBy : 0 ≤ By) (hH : 0 < H)
    (hαmin : 1 < αmin) (hαrange : αmin ≤ αmax) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, αmin ≤ α → α ≤ αmax →
      ∀ c : F, c ≠ 0 → HasDenominatorBound F D c →
        IsBalancedHeights F Bc (fun w => ‖w.embedding c‖) →
      ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
        IsBalancedHeights F By y → H ≤ ∏ w, y w →
        Summable (fun a : DenominatorScalars (F := F) D =>
          siegelRowKernel (c, a.1) x y α) ∧
        (∑' a : DenominatorScalars (F := F) D, siegelRowKernel (c, a.1) x y α) ≤
          C * Real.rpow (∏ w, y w) (2 - α) *
            Real.rpow (absFieldNorm F c) (1 - α) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
