import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.finite_denominator_elements_with_embedding_bounds
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.cusp_stabilizer_form_without_freeness
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.cusp_representatives_transition_eq

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Above a common product-height threshold, the remaining Siegel overlaps are finite.
Guide: sol-thin-spec/PROOFS.md:205. Uses R6_two_heights, G1_h3_basics, G2_x_action,
cusp_representatives_transition_eq, cusp_stabilizer_form_without_freeness,
finite_integral_elements_with_embedding_bounds and
finite_denominator_elements_with_embedding_bounds; feeds R9_proper. -/
theorem siegel_high_height_overlap_finite (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    ∃ A : ℝ, 0 ≤ A ∧ (siegelHighOverlap Γ d A).Finite := by
  sorry
end ArtinPrimitiveRoots.A1.Spec
