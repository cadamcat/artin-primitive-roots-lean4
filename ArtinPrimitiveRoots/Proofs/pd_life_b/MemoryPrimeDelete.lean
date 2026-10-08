import ArtinPrimitiveRoots.Proofs.pd_life_b.MemoryPrimeIndex

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD

private theorem deletion_survivors_sublist (l : List Particle)
    (D : Finset (Fin l.length)) : List.Sublist (removeIndices l D) l := by
  classical
  let p : Fin l.length → Bool := fun k => decide (k ∉ D)
  have hFilter : removeIndices l D = ((List.finRange l.length).filter p).map l.get := by
    unfold removeIndices
    rw [← List.filterMap_eq_map, List.filterMap_filter]
    apply congrArg (fun q => (List.finRange l.length).filterMap q)
    funext k
    by_cases hk : k ∈ D <;> simp [p, hk]
  rw [hFilter]
  have hsub := (List.filter_sublist (p := p) (l := List.finRange l.length)).map l.get
  simpa only [← List.ofFn_eq_map, List.ofFn_get] using hsub

/-- Deleting old indices subtracts their prime set and preserves the exact memory size. -/
theorem memory_prime_deletion_transport (l : List Particle)
    (h : (l.map Prod.fst).Nodup)
    (D : Finset (Fin l.length)) :
    ((removeIndices l D).map Prod.fst).toFinset =
      (l.map Prod.fst).toFinset \ D.image (fun k => (l.get k).1) ∧
    (removeIndices l D).length = l.length - D.card := by
  classical
  obtain ⟨e, he⟩ := memory_prime_index_equiv l h
  let g : Fin l.length → ℕ := fun k => (l.get k).1
  have hg : Function.Injective g := by
    intro k m hkm
    apply e.injective
    apply Subtype.ext
    rw [he k, he m]
    exact hkm
  have hAll : Finset.univ.image g = (l.map Prod.fst).toFinset := by
    apply Finset.ext
    intro p
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset,
      List.mem_map, g] using
      (List.exists_mem_iff_get (l := l) (p := fun v => v.1 = p)).symm
  have hRemove : ((removeIndices l D).map Prod.fst).toFinset =
      (Finset.univ \ D).image g := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      rcases List.mem_map.mp (List.mem_toFinset.mp hp) with ⟨v, hv, hp⟩
      rcases List.mem_filterMap.mp hv with ⟨k, _, hk⟩
      by_cases hd : k ∈ D
      · simp [hd] at hk
      · have hget : l.get k = v := by simpa [hd] using hk
        exact Finset.mem_image.mpr ⟨k,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hd⟩,
          (congrArg Prod.fst hget).trans hp⟩
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨k, hk, hkp⟩
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      refine ⟨l.get k, ?_, hkp⟩
      apply List.mem_filterMap.mpr
      refine ⟨k, List.mem_finRange k, ?_⟩
      simp [(Finset.mem_sdiff.mp hk).2]
  constructor
  · rw [hRemove, Finset.image_sdiff _ _ hg, hAll]
  · have hNodup : ((removeIndices l D).map Prod.fst).Nodup :=
      ((deletion_survivors_sublist l D).map Prod.fst).nodup h
    calc
      (removeIndices l D).length =
          (((removeIndices l D).map Prod.fst).toFinset).card := by
        rw [List.toFinset_card_of_nodup hNodup, List.length_map]
      _ = ((Finset.univ \ D).image g).card := congrArg Finset.card hRemove
      _ = (Finset.univ \ D).card := Finset.card_image_of_injective _ hg
      _ = l.length - D.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),
          Finset.card_univ, Fintype.card_fin]

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
