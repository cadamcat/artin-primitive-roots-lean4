import ArtinPrimitiveRoots.Proofs.pd_life_b.TraceGhostDeletions

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- A ghost-deleted prime is absent from the group's active and pending output. -/
theorem subsetGhostPoint_deleted_prime_absent {K : ℕ}
    (F : PDFix K) (S : PDScale) (j : ℕ) (σ : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (σ.1.2.2 i).length))
    (T : (i : Fin K) → (primeBand S.x (F.a i)).powerset)
    (hσ : LiveLogValid σ)
    (hlog : ((subsetGhostPoint F S j σ D T).2.map Prod.snd).Nodup)
    (i : Fin K) (r : Fin (σ.1.2.2 i).length) (hr : r ∈ D i) :
    ((σ.1.2.2 i).get r).1 ∉
      groupLivePrimes (subsetGhostPoint F S j σ D T).1 i := by
  classical
  let p := ((σ.1.2.2 i).get r).1
  have hpMem : p ∈ (σ.1.2.2 i).map Prod.fst :=
    List.mem_map.mpr ⟨(σ.1.2.2 i).get r, List.get_mem _ r, rfl⟩
  have hpLog : p ∈ σ.2.map Prod.snd :=
    hσ.2 i p (List.mem_append.mpr (Or.inr hpMem))
  have hpDel : p ∈ (D i).image (fun k => ((σ.1.2.2 i).get k).1) :=
    Finset.mem_image.mpr ⟨r, hr, rfl⟩
  have hLog :
      (subsetGhostPoint F S j σ D T).2.map Prod.snd =
        σ.2.map Prod.snd ++ (List.finRange K).flatMap (fun a => (T a).1.toList) := by
    simp only [subsetGhostPoint, List.map_append, List.map_flatMap, List.map_map]
    congr 1
    apply congrArg (List.finRange K).flatMap
    funext a
    change (T a).1.toList.zipIdx.map Prod.fst = (T a).1.toList
    exact List.zipIdx_map_fst 0 _
  rw [hLog] at hlog
  have hpFresh : p ∉ (T i).1 := by
    intro hp
    exact List.disjoint_left.mp (List.disjoint_of_nodup_append hlog) hpLog
      (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, Finset.mem_toList.mpr hp⟩)
  intro hp
  rcases List.mem_append.mp hp with hpActive | hpPending
  · change p ∈ List.ofFn (σ.1.2.1 i) at hpActive
    exact List.disjoint_left.mp (List.disjoint_of_nodup_append (hσ.1 i))
      hpActive hpMem
  · have hpSet := List.mem_toFinset.mpr hpPending
    rw [(ghost_memory_prime_transport F S j σ D T hσ i).1] at hpSet
    rcases Finset.mem_union.mp hpSet with hpOld | hpNew
    · exact (Finset.mem_sdiff.mp hpOld).2 hpDel
    · exact hpFresh hpNew

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
