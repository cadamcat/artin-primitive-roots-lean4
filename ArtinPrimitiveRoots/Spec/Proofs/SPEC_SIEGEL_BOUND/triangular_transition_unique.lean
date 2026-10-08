import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Two triangular transitions represent the same seed coset. Guide:
`sol-thin-spec/PROOFS.md:350`. Uses the frozen `cuspStab`/right-coset definitions;
feeds the first conjunct of `E4_eis_siegel`. -/
theorem triangular_transition_unique (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ σ' : SL(2,F)) (q q' : CuspCosets F Γ σ)
    (hq : siegelTransition Γ σ σ' q ∈ borelSL F)
    (hq' : siegelTransition Γ σ σ' q' ∈ borelSL F) : q = q' := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
