import ArtinPrimitiveRoots.Proofs.pd_life_b.SymmetryLive

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD

/-- Distinct memory prime values identify their old list indices uniquely. -/
theorem memory_prime_index_equiv (l : List Particle)
    (h : (l.map Prod.fst).Nodup) :
    ∃ e : Fin l.length ≃ {p : ℕ // p ∈ (l.map Prod.fst).toFinset},
      ∀ k : Fin l.length, (e k).val = (l.get k).1 := by
  classical
  let f : Fin l.length → {p : ℕ // p ∈ (l.map Prod.fst).toFinset} := fun k =>
    ⟨(l.get k).1, List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨l.get k, List.get_mem l k, rfl⟩)⟩
  have hIndex : Function.Injective (fun k : Fin l.length => (l.get k).1) := by
    apply List.nodup_ofFn.mp
    change (List.ofFn (Prod.fst ∘ l.get)).Nodup
    rw [← List.map_ofFn, List.ofFn_get]
    exact h
  have hf : Function.Bijective f := by
    constructor
    · intro k m hkm
      exact hIndex (congrArg Subtype.val hkm)
    · intro p
      obtain ⟨k, hk⟩ := List.exists_mem_iff_get.mp
        (List.mem_map.mp (List.mem_toFinset.mp p.property))
      exact ⟨k, Subtype.ext hk⟩
  refine ⟨Equiv.ofBijective f hf, ?_⟩
  intro k
  rfl

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
