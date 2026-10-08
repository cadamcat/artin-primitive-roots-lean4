import ArtinPrimitiveRoots.Proofs.pd_life_b.GhostDeletedAbsent

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- A ghost step cannot revive an absent prime already recorded in the birth log. -/
theorem subsetGhostPoint_prime_absent_of_logged {K : ℕ}
    (F : PDFix K) (S : PDScale) (j : ℕ) (σ : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (σ.1.2.2 i).length))
    (T : (i : Fin K) → (primeBand S.x (F.a i)).powerset)
    (hσ : LiveLogValid σ)
    (hlog : ((subsetGhostPoint F S j σ D T).2.map Prod.snd).Nodup)
    (i : Fin K) (p : ℕ)
    (hpLog : p ∈ σ.2.map Prod.snd)
    (hpAbsent : p ∉ groupLivePrimes σ.1 i) :
    p ∉ groupLivePrimes (subsetGhostPoint F S j σ D T).1 i := by
  classical
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
    exact hpAbsent (List.mem_append.mpr (Or.inl hpActive))
  · have hpSet := List.mem_toFinset.mpr hpPending
    rw [(ghost_memory_prime_transport F S j σ D T hσ i).1] at hpSet
    rcases Finset.mem_union.mp hpSet with hpOld | hpNew
    · exact hpAbsent (List.mem_append.mpr
        (Or.inr (List.mem_toFinset.mp (Finset.mem_sdiff.mp hpOld).1)))
    · exact hpFresh hpNew

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
