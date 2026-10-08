import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Scalar norm weights converge on any family with distinct unit orbits for
exponent greater than one. Guide: `sol-thin-spec/PROOFS.md:358`, scalar variant of
R5. Uses `R4_unit_balance` and Mathlib scalar lattice p-series; feeds
`balanced_denominator_rows_bound`. The row theorem R5 alone has too large a threshold. -/
theorem scalar_unit_orbit_summable (D : ℕ) (hD : 0 < D) (β : ℝ) (hβ : 1 < β)
    {ι : Type*} (c : ι → F)
    (hcD : ∀ i, HasDenominatorBound F D (c i)) (hc0 : ∀ i, c i ≠ 0)
    (huniq : ∀ i j, scalarUnitAssociated (c i) (c j) → i = j) :
    Summable (fun i => Real.rpow (absFieldNorm F (c i)) (-β)) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
