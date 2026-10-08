import ArtinPrimitiveRoots.Proofs.pd_life_b.GhostAbsentPreservation

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- An edge step cannot revive an absent prime already recorded in the birth log. -/
theorem edgeOutputPoint_prime_absent_of_logged {K : ℕ}
    (F : PDFix K) (S : PDScale) (step : ℕ) (σ : LogPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (σ.1.2.2 i) i)
    (z' : ℤ × ℤ) (hσ : LiveLogValid σ)
    (hlog : ((edgeOutputPoint F S step σ c z').2.map Prod.snd).Nodup)
    (i : Fin K) (p : ℕ)
    (hpLog : p ∈ σ.2.map Prod.snd)
    (hpAbsent : p ∉ groupLivePrimes σ.1 i) :
    p ∉ groupLivePrimes (edgeOutputPoint F S step σ c z').1 i := by
  classical
  have hLog : (edgeOutputPoint F S step σ c z').2.map Prod.snd =
      σ.2.map Prod.snd ++ (edgeBirths F S step σ.1 c).map Prod.snd := by
    simp only [edgeOutputPoint, List.map_append]
  rw [hLog] at hlog
  have hFresh := List.disjoint_of_nodup_append hlog
  have hBirth (q : primeBand S.x (F.a i)) (hc : (c i).2 = Sum.inr q) :
      (q : ℕ) ∈ (edgeBirths F S step σ.1 c).map Prod.snd := by
    apply List.mem_map.mpr
    refine ⟨(BirthAddress.edge step i, (q : ℕ)), ?_, rfl⟩
    unfold edgeBirths
    apply List.mem_flatMap.mpr
    exact ⟨i, List.mem_finRange i, by simp [hc]⟩
  have hOldActive (j : Fin (slotCount S.x)) (hj : σ.1.2.1 i j = p) : False :=
    hpAbsent (List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨j, hj⟩)))
  have hOldPending (hp : p ∈ (σ.1.2.2 i).map Prod.fst) : False :=
    hpAbsent (List.mem_append.mpr (Or.inr hp))
  intro hp
  rcases List.mem_append.mp hp with hpActive | hpPending
  · rcases List.mem_ofFn.mp hpActive with ⟨j, hjp⟩
    change edgeTargetLists F S σ.1 c i j = p at hjp
    by_cases hj : j.val < momentJ S.x
    · exact hOldActive j (by simpa only [edgeTargetLists, ite_eq_left hj] using hjp)
    · have hNew : edgeNewLabel (c i) = p := by
        simpa only [edgeTargetLists, ite_eq_right hj] using hjp
      cases hc : (c i).2 with
      | inl r =>
          apply hOldPending
          exact List.mem_map.mpr ⟨(σ.1.2.2 i).get r, List.get_mem _ r,
            by simpa only [edgeNewLabel, hc] using hNew⟩
      | inr q =>
          have hqp : (q : ℕ) = p := by simpa only [edgeNewLabel, hc] using hNew
          exact List.disjoint_left.mp hFresh hpLog (hqp ▸ hBirth q hc)
  · change p ∈ (edgeNewMemory F S σ.1 c i).map Prod.fst at hpPending
    have hpSet := List.mem_toFinset.mpr hpPending
    rw [(edge_memory_prime_transport F S σ c hσ i).1] at hpSet
    rcases Finset.mem_union.mp hpSet with hpOld | hpStore
    · exact hOldPending (List.mem_toFinset.mp (Finset.mem_sdiff.mp hpOld).1)
    · cases hb : (c i).1 with
      | false => simp [hb] at hpStore
      | true =>
          have hpp : p = σ.1.2.1 i (lastSlot S.x) := by simpa [hb] using hpStore
          exact hOldActive (lastSlot S.x) hpp.symm

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
