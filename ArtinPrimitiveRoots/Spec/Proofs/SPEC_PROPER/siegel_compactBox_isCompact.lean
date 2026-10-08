import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- A bounded product height in a balanced cusp chart gives a compact box.
Guide: sol-thin-spec/PROOFS.md:204 and 230–234 (R13 first conjunct only).
Uses G1_h3_basics, R3_cusps_finite for the positive lower height, and d.P_bounded;
feeds siegel_low_height_overlap_finite without using R13's orbit-cover conclusion. -/
theorem siegel_compactBox_isCompact (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 ≤ A) (i : d.ι) :
    IsCompact (SiegelData.compactBox F d i A) := by
  sorry
end ArtinPrimitiveRoots.A1.Spec
