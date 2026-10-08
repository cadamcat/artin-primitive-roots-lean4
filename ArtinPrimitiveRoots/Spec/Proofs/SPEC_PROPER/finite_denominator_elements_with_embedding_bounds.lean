import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.finite_integral_elements_with_embedding_bounds

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- A common positive integral denominator and bounded embeddings give a finite field set.
Guide: sol-thin-spec/PROOFS.md:205, denominator step. Uses
finite_integral_elements_with_embedding_bounds; feeds siegel_high_height_overlap_finite. -/
theorem finite_denominator_elements_with_embedding_bounds (D : ℕ) (hD : 0 < D)
    (R : ℝ) (hR : 0 ≤ R) :
    {μ : F | HasDenominatorBound F D μ ∧
      ∀ w : InfinitePlace F, ‖w.embedding μ‖ ≤ R}.Finite := by
  sorry
end ArtinPrimitiveRoots.A1.Spec
