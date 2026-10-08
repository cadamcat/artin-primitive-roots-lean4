import ArtinPrimitiveRoots.Proofs.pd_life_b.GhostDeletionUnique

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- Disjoint group bands make all ghost-deleted prime values distinct. -/
theorem finiteHistoryTrace_ghost_deletions_nodup_prime {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t)
    (hσ : LiveLogValid σ) (hMem : MemValid F S σ.1)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i'))) :
    ((finiteHistoryTraceGhostDeletions F S γ k σ t).map
      (fun d => d.2.2.1)).Nodup := by
  have hKeys := finiteHistoryTrace_ghost_deletions_nodup_group_prime
    F S w γ k σ t ht hσ
  have hData := finiteHistoryTrace_ghost_deletion_data F S w γ k σ t ht hMem
  have hPrime : (((finiteHistoryTraceGhostDeletions F S γ k σ t).map
      (fun d => (d.2.1, d.2.2.1))).map Prod.snd).Nodup := by
    apply hKeys.map_on
    intro a ha b hb hp
    rcases List.mem_map.mp ha with ⟨d, hd, rfl⟩
    rcases List.mem_map.mp hb with ⟨e, he, rfl⟩
    change d.2.2.1 = e.2.2.1 at hp
    have hg : d.2.1 = e.2.1 := by
      by_contra hne
      have hdBand := (hData d hd).1
      have heBand := (hData e he).1
      rw [← hp] at heBand
      exact Finset.disjoint_left.mp (hBands d.2.1 e.2.1 hne) hdBand heBand
    exact Prod.ext hg hp
  simpa only [List.map_map, Function.comp_def] using hPrime

/-- A deleted prime identifies its unique ghost-deletion event. -/
theorem finiteHistoryTrace_ghost_deletion_eq_of_prime_eq {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t)
    (hσ : LiveLogValid σ) (hMem : MemValid F S σ.1)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    {d e : Fin (pathLength S.x + 1) × Fin K × Particle}
    (hd : d ∈ finiteHistoryTraceGhostDeletions F S γ k σ t)
    (he : e ∈ finiteHistoryTraceGhostDeletions F S γ k σ t)
    (hprime : d.2.2.1 = e.2.2.1) : d = e := by
  let D := finiteHistoryTraceGhostDeletions F S γ k σ t
  have hKeys : (D.map fun d => (d.2.1, d.2.2.1)).Nodup :=
    finiteHistoryTrace_ghost_deletions_nodup_group_prime
      F S w γ k σ t ht hσ
  have hD : D.Nodup := hKeys.of_map
  have hPrime : (D.map fun d => d.2.2.1).Nodup := by
    simpa only [List.map_map, Function.comp_def] using
      (finiteHistoryTrace_ghost_deletions_nodup_prime
        F S w γ k σ t ht hσ hMem hBands)
  have hInj := (List.nodup_map_iff_inj_on hD).1 hPrime
  exact hInj d (by simpa [D] using hd) e (by simpa [D] using he) hprime

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
