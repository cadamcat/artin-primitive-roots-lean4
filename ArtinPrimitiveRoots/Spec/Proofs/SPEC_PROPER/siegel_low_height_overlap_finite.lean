import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.compact_overlap_finite_SL2O
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.siegel_compactBox_isCompact

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Low-height Siegel overlaps lie in finitely many pairs of compact cusp boxes.
Guide: sol-thin-spec/PROOFS.md:204. Uses siegel_compactBox_isCompact and
compact_overlap_finite_SL2O; feeds R9_proper. -/
theorem siegel_low_height_overlap_finite (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 ≤ A) :
    (siegelLowOverlap Γ d A).Finite := by
  sorry
end ArtinPrimitiveRoots.A1.Spec
