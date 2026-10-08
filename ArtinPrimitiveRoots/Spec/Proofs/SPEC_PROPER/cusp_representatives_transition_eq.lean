import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- A triangular transition between distinct entries of the cusp representative system
forces equality of their indices.
Guide: sol-thin-spec/PROOFS.md:205. Uses d.reps_bijective and the right-coset
relations underlying R3_cusps_finite; feeds siegel_high_height_overlap_finite. -/
theorem cusp_representatives_transition_eq
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (d : SiegelData F Γ)
    (i j : d.ι) (γ : Γ)
    (htri : (d.σ j)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * d.σ i ∈ borelSL F) :
    i = j := by
  sorry
end ArtinPrimitiveRoots.A1.Spec
