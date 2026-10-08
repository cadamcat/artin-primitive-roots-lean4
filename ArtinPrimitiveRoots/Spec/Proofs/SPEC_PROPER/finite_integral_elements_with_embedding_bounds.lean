import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Integral elements with uniformly bounded chosen complex embeddings form a finite set.
Guide: sol-thin-spec/PROOFS.md:202. Uses the Mathlib canonical embedding lattice;
feeds compact_overlap_finite_SL2O, finite_denominator_elements_with_embedding_bounds,
and siegel_high_height_overlap_finite. -/
theorem finite_integral_elements_with_embedding_bounds (R : ℝ) (hR : 0 ≤ R) :
    {a : 𝓞 F | ∀ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F a)‖ ≤ R}.Finite := by
  sorry
end ArtinPrimitiveRoots.A1.Spec
