import ArtinPrimitiveRoots.Proofs.spec_proper_b.Topology

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
  letI : LocallyCompactSpace (X F) := SpecProperB.locallyCompactX
  letI : T2Space (X F) := SpecProperB.t2SpaceX
  obtain ⟨C, hC, hzC, hCV⟩ := exists_compact_subset hV hz
  let U : Set (X F) := interior C
  have hclosureC : closure U ⊆ C := by
    apply closure_minimal interior_subset hC.isClosed
  have hclosureCompact : IsCompact (closure U) :=
    IsCompact.of_isClosed_subset hC isClosed_closure hclosureC
  let T : Set (SL(2,𝓞 F)) := {γ | ∃ x ∈ K, γ • x ∈ closure U}
  have hOverlap : T.Finite := compact_overlap_finite_SL2O K (closure U) hK hclosureCompact
  refine ⟨U, isOpen_interior, hzC, hclosureC.trans hCV, hclosureCompact, ?_⟩
  refine Set.Finite.of_injOn (f := fun γ : Γ => (γ : SL(2,𝓞 F)))
    (s := {γ : Γ | ∃ x ∈ K, (γ : SL(2,𝓞 F)) • x ∈ closure U}) (t := T) ?_ ?_ ?_
  · intro γ hγ
    exact hγ
  · intro γ _ γ' _ hγγ'
    exact Subtype.ext hγγ'
  · exact hOverlap
end ArtinPrimitiveRoots.A1.Spec
