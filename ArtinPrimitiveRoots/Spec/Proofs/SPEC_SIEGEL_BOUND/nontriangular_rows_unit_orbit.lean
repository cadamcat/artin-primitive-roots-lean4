import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Nontriangular cosets give denominator-bounded rows with nonzero first entry
and no repeated unit orbit. Guide: `sol-thin-spec/PROOFS.md:351`. Uses `E1_eis_def`;
feeds `nontriangular_siegel_summable`. -/
theorem nontriangular_rows_unit_orbit (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ σ' : SL(2,F)) :
    ∃ D : ℕ, 0 < D ∧
      (∀ q : NontriangularCosets Γ σ σ',
        let v := bottomRow F (siegelTransition Γ σ σ' q.1)
        v.1 ≠ 0 ∧ HasDenominatorBound F D v.1 ∧ HasDenominatorBound F D v.2) ∧
      (∀ q q' : NontriangularCosets Γ σ σ',
        unitAssociatedRows F
          (bottomRow F (siegelTransition Γ σ σ' q.1))
          (bottomRow F (siegelTransition Γ σ σ' q'.1)) → q = q') := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
