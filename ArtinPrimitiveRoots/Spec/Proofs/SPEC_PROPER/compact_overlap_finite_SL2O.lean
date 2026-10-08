import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.finite_integral_elements_with_embedding_bounds

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Only finitely many integral determinant-one matrices move one compact set to meet another.
Guide: sol-thin-spec/PROOFS.md:203. Uses G1_h3_basics, G2_x_action and
finite_integral_elements_with_embedding_bounds; feeds R9_proper, low-height finiteness,
free_action_wandering_nbhd and local_finite_overlap. -/
theorem compact_overlap_finite_SL2O (K K' : Set (X F))
    (hK : IsCompact K) (hK' : IsCompact K') :
    {γ : SL(2,𝓞 F) | ∃ z ∈ K, γ • z ∈ K'}.Finite := by
  sorry
end ArtinPrimitiveRoots.A1.Spec
