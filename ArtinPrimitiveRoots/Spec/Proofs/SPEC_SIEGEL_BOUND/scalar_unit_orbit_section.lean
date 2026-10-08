import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Choose one balanced nonzero scalar per unit orbit in the denominator lattice.
The covering witness rescales by a unit; its torsion ambiguity is harmless.
Guide: `sol-thin-spec/PROOFS.md:352`. Uses `R4_unit_balance`; feeds
`balanced_denominator_rows_bound`. -/
theorem scalar_unit_orbit_section (D : ℕ) (hD : 0 < D) :
    ∃ (B : ℝ) (S : Set F), 0 ≤ B ∧
      (∀ c ∈ S, c ≠ 0 ∧ HasDenominatorBound F D c ∧
        IsBalancedHeights F B (fun w => ‖w.embedding c‖)) ∧
      (∀ c c', c ∈ S → c' ∈ S → scalarUnitAssociated c c' → c = c') ∧
      (∀ c : F, c ≠ 0 → HasDenominatorBound F D c →
        ∃ ε : (𝓞 F)ˣ, algebraMap (𝓞 F) F (ε : 𝓞 F) * c ∈ S) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
