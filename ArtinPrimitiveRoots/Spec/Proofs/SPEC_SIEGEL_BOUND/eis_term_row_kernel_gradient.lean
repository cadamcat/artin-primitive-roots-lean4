import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- A transitioned term has the real row-kernel norm and gradient norm equal to
`|1+2s| sqrt(r)` times its norm. Guide: `sol-thin-spec/PROOFS.md:351,353`.
Uses `G2_x_action`, `G4_energy` and the chain rule for the positive height cpow;
feeds `nontriangular_siegel_summable`. No restriction on s is needed for a single term. -/
theorem eis_term_row_kernel_gradient (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ σ' : SL(2,F)) (s : ℂ) (q : CuspCosets F Γ σ) (z : X F) :
    ‖eisTerm F Γ σ s (σ' • z) q‖ =
      siegelRowKernel (bottomRow F (siegelTransition Γ σ σ' q))
        (fun w => horiz (z w)) (fun w => height (z w)) (1 + 2 * s.re) ∧
    ‖fullGradient F (fun x => eisTerm F Γ σ s (σ' • x) q) z‖ =
      ‖1 + 2 * s‖ * Real.sqrt (placeCount F) * ‖eisTerm F Γ σ s (σ' • z) q‖ := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
