import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.nontriangular_rows_unit_orbit
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.balanced_denominator_rows_bound
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.eis_term_row_kernel_gradient

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Assemble the uniformly summable nontriangular terms and gradients on one
Siegel set. Guide: `sol-thin-spec/PROOFS.md:351,358–360`. Uses
`nontriangular_rows_unit_orbit`, `balanced_denominator_rows_bound`, and
`eis_term_row_kernel_gradient`; feeds the second conjunct of `E4_eis_siegel`.
For a nonempty parameter compactum use the extrema of `1+2 Re(s)` and `|1+2s|`;
for a nonempty Siegel set its balance constant is nonnegative and lowerHeight positive.
Empty parameter or Siegel sets give C=0. -/
theorem nontriangular_siegel_summable (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (σ : SL(2,F))
    (Kₛ : Set ℂ) (hKₛ : IsCompact Kₛ)
    (hKₛstrip : Kₛ ⊆ {s : ℂ | 2 < s.re ∧ s.re < 3}) (i : d.ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Kₛ, ∀ z ∈ SiegelData.setAt F d i,
      Summable (fun q : NontriangularCosets Γ σ (d.σ i) =>
        ‖eisTerm F Γ σ s ((d.σ i) • z) q.1‖ +
          ‖fullGradient F (fun x => eisTerm F Γ σ s ((d.σ i) • x) q.1) z‖) ∧
      (∑' q : NontriangularCosets Γ σ (d.σ i),
        (‖eisTerm F Γ σ s ((d.σ i) • z) q.1‖ +
          ‖fullGradient F (fun x => eisTerm F Γ σ s ((d.σ i) • x) q.1) z‖)) ≤ C := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
