import ArtinPrimitiveRoots.Proofs.pd_life_b.MemoryPrimeDelete

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD

/-- Prime-set reindexing preserves the ghost deletion guard and both scalar exponents. -/
theorem memory_prime_hits_transport (l : List Particle)
    (h : (l.map Prod.fst).Nodup) (z : ℤ × ℤ)
    (D : Finset (Fin l.length)) :
    (D ⊆ hitIndices l z ↔
      D.image (fun k => (l.get k).1) ⊆
        (hitIndices l z).image (fun k => (l.get k).1)) ∧
    ((hitIndices l z).image (fun k => (l.get k).1)).card = hitCount l z ∧
    (D.image (fun k => (l.get k).1)).card = D.card := by
  classical
  obtain ⟨e, he⟩ := memory_prime_index_equiv l h
  let g : Fin l.length → ℕ := fun k => (l.get k).1
  have hg : Function.Injective g := by
    intro k m hkm
    apply e.injective
    apply Subtype.ext
    rw [he k, he m]
    exact hkm
  constructor
  · exact (Finset.image_subset_image_iff hg).symm
  · exact ⟨Finset.card_image_of_injective (hitIndices l z) hg,
      Finset.card_image_of_injective D hg⟩

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
