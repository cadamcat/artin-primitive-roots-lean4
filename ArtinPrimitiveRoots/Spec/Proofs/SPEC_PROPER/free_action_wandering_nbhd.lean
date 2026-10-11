import ArtinPrimitiveRoots.Proofs.spec_proper_b.Topology

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- A free arithmetic action has an open neighborhood disjoint from each nonidentity translate.
Uses G1_h3_basics, G2_x_action and
compact_overlap_finite_SL2O; feeds R9_proper. -/
theorem free_action_wandering_nbhd (Γ : Subgroup SL(2,𝓞 F))
    (hfree : FreeAction F Γ) (z : X F) :
    ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧
      ∀ γ : Γ, γ ≠ 1 → Disjoint ((fun x => (γ : SL(2,𝓞 F)) • x) '' U) U := by
  classical
  letI : LocallyCompactSpace (X F) := SpecProperB.locallyCompactX
  letI : T2Space (X F) := SpecProperB.t2SpaceX
  obtain ⟨K₀, hK₀, hK₀mem⟩ := exists_compact_mem_nhds z
  obtain ⟨W, hWK₀, hWopen, hzW⟩ := mem_nhds_iff.mp hK₀mem
  let T : Set (SL(2,𝓞 F)) := {g | ∃ x ∈ K₀, g • x ∈ K₀}
  have hOverlap : T.Finite := compact_overlap_finite_SL2O K₀ K₀ hK₀ hK₀
  let E : Set Γ := {γ | ∃ x ∈ K₀, (γ : SL(2,𝓞 F)) • x ∈ K₀}
  have hE : E.Finite := by
    refine Set.Finite.of_injOn (f := fun γ : Γ => (γ : SL(2,𝓞 F)))
      (s := E) (t := T) ?_ ?_ ?_
    · intro γ hγ
      exact hγ
    · intro γ _ γ' _ hγγ'
      exact Subtype.ext hγγ'
    · exact hOverlap
  have hsep (γ : Γ) (hγ1 : γ ≠ 1) :
      ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧
        Disjoint ((fun x => (γ : SL(2,𝓞 F)) • x) '' U) U := by
    have hzmove : z ≠ (γ : SL(2,𝓞 F)) • z := by
      intro hfix
      apply hγ1
      apply Subtype.ext
      exact hfree (γ : SL(2,𝓞 F)) γ.property z hfix.symm
    rcases t2_separation hzmove with
      ⟨Vz, Vgz, hVz, hVgz, hzVz, hgzVgz, hdisj⟩
    let U := Vz ∩ (fun x : X F => (γ : SL(2,𝓞 F)) • x) ⁻¹' Vgz
    refine ⟨U, hVz.inter (hVgz.preimage
      (SpecProperB.continuousSL2OAction (γ : SL(2,𝓞 F)))),
      ?_, ?_⟩
    · exact ⟨hzVz, hgzVgz⟩
    · rw [Set.disjoint_left]
      rintro y ⟨x, hx, rfl⟩ hy
      have hxy : (γ : SL(2,𝓞 F)) • x ∈ Vz ∩ Vgz := ⟨hy.1, hx.2⟩
      have hdisjInter : Vz ∩ Vgz = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
      simpa [hdisjInter] using hxy
  let sepU : Γ → Set (X F) := fun γ =>
    if hγE : γ ∈ E then
      if hγ1 : γ ≠ 1 then Classical.choose (hsep γ hγ1) else Set.univ
    else Set.univ
  let S : Set Γ := {γ | γ ∈ E ∧ γ ≠ 1}
  have hS : S.Finite := by
    apply hE.subset
    intro γ hγ
    exact hγ.1
  let U : Set (X F) := W ∩ ⋂ γ ∈ S, sepU γ
  have hsepU_open (γ : Γ) (hγ : γ ∈ S) : IsOpen (sepU γ) := by
    change γ ∈ E ∧ γ ≠ 1 at hγ
    simp only [sepU, dif_pos hγ.1, dif_pos hγ.2]
    exact (Classical.choose_spec (hsep γ hγ.2)).1
  have hUopen : IsOpen U := by
    dsimp [U]
    exact hWopen.inter (hS.isOpen_biInter hsepU_open)
  have hzU : z ∈ U := by
    refine ⟨hzW, Set.mem_iInter₂.mpr ?_⟩
    intro γ hγ
    change γ ∈ E ∧ γ ≠ 1 at hγ
    simp only [sepU, dif_pos hγ.1, dif_pos hγ.2]
    exact (Classical.choose_spec (hsep γ hγ.2)).2.1
  have hUsubK₀ : U ⊆ K₀ := by
    intro x hx
    exact hWK₀ hx.1
  refine ⟨U, hUopen, hzU, ?_⟩
  intro γ hγ1
  by_cases hγE : γ ∈ E
  · have hγS : γ ∈ S := ⟨hγE, hγ1⟩
    have hUsubSep : U ⊆ sepU γ := by
      intro x hx
      exact (Set.mem_iInter₂.mp hx.2) γ hγS
    have hsepSets : Disjoint
        ((fun x => (γ : SL(2,𝓞 F)) • x) '' sepU γ) (sepU γ) := by
      simp only [sepU, dif_pos hγE, dif_pos hγ1]
      exact (Classical.choose_spec (hsep γ hγ1)).2.2
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    exact (Set.disjoint_left.mp hsepSets) ⟨x, hUsubSep hx, rfl⟩ (hUsubSep hy)
  · rw [Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    exact hγE ⟨x, hUsubK₀ hx, hUsubK₀ hy⟩
end ArtinPrimitiveRoots.A1.Spec
