import ArtinPrimitiveRoots.Proofs.pd_life_b.IndexTransport
import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD

/-- Reindexing a memory list preserves its hitting particles, their count, and the
permutation class of survivors after the corresponding deletion subset. -/
theorem memory_index_transport (l m : List Particle) (z : ℤ × ℤ)
    (e : Fin l.length ≃ Fin m.length)
    (he : ∀ k, l.get k = m.get (e k))
    (D : Finset (Fin l.length)) :
    (hitIndices l z).map e.toEmbedding = hitIndices m z ∧
      hitCount l z = hitCount m z ∧
      (removeIndices l D).Perm
        (removeIndices m (D.map e.toEmbedding)) := by
  classical
  have hHits : (hitIndices l z).map e.toEmbedding = hitIndices m z := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_map_equiv, hitIndices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [he (e.symm j), e.apply_symm_apply]
  have hCount : hitCount l z = hitCount m z := by
    unfold hitCount
    rw [← hHits, Finset.card_map]
  have hRange : ((List.finRange l.length).map e).Perm (List.finRange m.length) := by
    apply (List.perm_ext_iff_of_nodup
      ((List.nodup_finRange l.length).map e.injective)
      (List.nodup_finRange m.length)).mpr
    intro j
    simp only [List.mem_map, List.mem_finRange, true_and]
    exact ⟨fun _ => True.intro, fun _ => e.surjective j⟩
  let g : Fin m.length → Option Particle := fun j =>
    if j ∈ D.map e.toEmbedding then none else some (m.get j)
  have hFunctions : g ∘ e = fun k => if k ∈ D then none else some (l.get k) := by
    funext k
    simp only [Function.comp_apply, g, Finset.mem_map_equiv,
      Equiv.symm_apply_apply, ← he k]
  have hRemoved := hRange.filterMap g
  rw [List.filterMap_map, hFunctions] at hRemoved
  exact ⟨hHits, hCount, by simpa only [removeIndices, g] using hRemoved⟩

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
