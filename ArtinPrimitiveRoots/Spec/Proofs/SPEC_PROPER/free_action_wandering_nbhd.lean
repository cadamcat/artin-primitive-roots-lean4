import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.compact_overlap_finite_SL2O

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- A free arithmetic action has an open neighborhood disjoint from each nonidentity translate.
Guide: sol-thin-spec/PROOFS.md:206. Uses G1_h3_basics, G2_x_action and
compact_overlap_finite_SL2O; feeds R9_proper. -/
theorem free_action_wandering_nbhd (Γ : Subgroup SL(2,𝓞 F))
    (hfree : FreeAction F Γ) (z : X F) :
    ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧
      ∀ γ : Γ, γ ≠ 1 → Disjoint ((fun x => (γ : SL(2,𝓞 F)) • x) '' U) U := by
  sorry
end ArtinPrimitiveRoots.A1.Spec
