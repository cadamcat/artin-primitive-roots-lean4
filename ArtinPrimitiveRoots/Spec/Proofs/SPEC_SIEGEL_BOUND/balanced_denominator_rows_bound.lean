import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.scalar_unit_orbit_section
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.scalar_unit_orbit_summable
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.balanced_first_coordinate_fiber_bound

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- The row-kernel sum is uniformly bounded on balanced positive heights with a
product floor, for any denominator-bounded row family with distinct unit orbits and
nonzero first coordinates. Guide: `sol-thin-spec/PROOFS.md:352,358`.
Uses `scalar_unit_orbit_section`, `scalar_unit_orbit_summable`, and
`balanced_first_coordinate_fiber_bound`; feeds `nontriangular_siegel_summable`.
Rescale each whole row to its chosen c representative, inject into the (c,d) family,
then split the c norm at one to use the two endpoint summable weights. -/
theorem balanced_denominator_rows_bound (D : ℕ) (hD : 0 < D)
    (By H αmin αmax : ℝ) (hBy : 0 ≤ By) (hH : 0 < H)
    (hαmin : 2 < αmin) (hαrange : αmin ≤ αmax) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, αmin ≤ α → α ≤ αmax →
      ∀ {ι : Type*} (v : ι → F × F),
        (∀ i, HasDenominatorBound F D (v i).1 ∧ HasDenominatorBound F D (v i).2) →
        (∀ i, (v i).1 ≠ 0) →
        (∀ i j, unitAssociatedRows F (v i) (v j) → i = j) →
      ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
        IsBalancedHeights F By y → H ≤ ∏ w, y w →
        Summable (fun i => siegelRowKernel (v i) x y α) ∧
          (∑' i, siegelRowKernel (v i) x y α) ≤ C := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
