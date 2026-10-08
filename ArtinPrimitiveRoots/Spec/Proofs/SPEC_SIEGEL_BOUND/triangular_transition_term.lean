import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- The triangular term has the absolute FIELD norm as its leading coefficient,
even when its diagonal entry is not integral. Guide: `sol-thin-spec/PROOFS.md:350`.
Uses `G2_x_action`; feeds the third conjunct of `E4_eis_siegel`. -/
theorem triangular_transition_term (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ σ' : SL(2,F)) (q : CuspCosets F Γ σ)
    (hq : siegelTransition Γ σ σ' q ∈ borelSL F) (s : ℂ) (z : X F) :
    eisTerm F Γ σ s (σ' • z) q =
      ((absFieldNorm F ((siegelTransition Γ σ σ' q) 0 0) : ℝ) : ℂ) ^ (1 + 2 * s) *
        ((normHeight F z : ℝ) : ℂ) ^ (1 + 2 * s) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
