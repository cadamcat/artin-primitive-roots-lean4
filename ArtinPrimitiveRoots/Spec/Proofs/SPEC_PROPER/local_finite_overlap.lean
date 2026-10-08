import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.compact_overlap_finite_SL2O

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- A compact support and an arbitrary open coordinate neighborhood admit a smaller
open neighborhood with compact closure and only finitely many intersecting translates.
Guide: sol-thin-spec/PROOFS.md:207–208. Uses G1_h3_basics and
compact_overlap_finite_SL2O; exported for periodization and kernel integrals. -/
theorem local_finite_overlap (Γ : Subgroup SL(2,𝓞 F))
    (K : Set (X F)) (hK : IsCompact K) (V : Set (X F)) (hV : IsOpen V)
    (z : X F) (hz : z ∈ V) :
    ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧ closure U ⊆ V ∧
      IsCompact (closure U) ∧
      {γ : Γ | ∃ x ∈ K, (γ : SL(2,𝓞 F)) • x ∈ closure U}.Finite := by
  sorry
end ArtinPrimitiveRoots.A1.Spec
