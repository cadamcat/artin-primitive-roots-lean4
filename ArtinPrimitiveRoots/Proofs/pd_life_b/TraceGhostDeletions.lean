import ArtinPrimitiveRoots.Proofs.pd_life_b.GhostBirthData

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- Ghost deletions of a complete trace, retaining each deleted particle and its visit/group. -/
def finiteHistoryTraceGhostDeletions {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) :
    (k : ℕ) → (σ : LogPoint S.x K) → FiniteHistoryTrace F S γ k σ →
      List (Fin (pathLength S.x + 1) × Fin K × Particle)
  | 0, σ, t =>
      (List.finRange K).flatMap fun i =>
        (t.1 i).toList.map fun r =>
          (Fin.last (pathLength S.x), i, (σ.1.2.2 i).get r)
  | k + 1, σ, t =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      ((List.finRange K).flatMap fun i =>
        (t.1.1 i).toList.map fun r =>
          ((⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ :
            Fin (pathLength S.x + 1)), i, (σ.1.2.2 i).get r)) ++
        finiteHistoryTraceGhostDeletions F S γ k υ t.2.2

/-- Deleted particles stay in their group bands and hit the recorded external visit. -/
theorem finiteHistoryTrace_ghost_deletion_data {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t)
    (hσ : MemValid F S σ.1) :
    ∀ d ∈ finiteHistoryTraceGhostDeletions F S γ k σ t,
      d.2.2.1 ∈ primeBand S.x (F.a d.2.1) ∧
        d.2.2.2 ≤ d.2.2.1 ∧ particleHits d.2.2 (γ d.1).1 := by
  have hBlock (v : Fin (pathLength S.x + 1)) (ω : LogPoint S.x K)
      (D : (i : Fin K) → Finset (Fin (ω.1.2.2 i).length))
      (hv : MemValid F S ω.1) (hVisit : ω.1.1 = (γ v).1)
      (hD : ∀ i, D i ⊆ hitIndices (ω.1.2.2 i) ω.1.1)
      (d : Fin (pathLength S.x + 1) × Fin K × Particle)
      (hd : d ∈ (List.finRange K).flatMap fun i =>
        (D i).toList.map fun r => (v, i, (ω.1.2.2 i).get r)) :
      d.2.2.1 ∈ primeBand S.x (F.a d.2.1) ∧
        d.2.2.2 ≤ d.2.2.1 ∧ particleHits d.2.2 (γ d.1).1 := by
    rcases List.mem_flatMap.mp hd with ⟨i, _, hi⟩
    rcases List.mem_map.mp hi with ⟨r, hr, rfl⟩
    have hData := hv.2.2 i ((ω.1.2.2 i).get r) (List.get_mem _ r)
    have hHit : particleHits ((ω.1.2.2 i).get r) ω.1.1 :=
      (Finset.mem_filter.mp (hD i (Finset.mem_toList.mp hr))).2
    rw [hVisit] at hHit
    exact ⟨hData.1, hData.2, hHit⟩
  induction k generalizing σ with
  | zero =>
      intro d hd
      exact hBlock (Fin.last (pathLength S.x)) σ t.1 hσ
        (congrArg Prod.fst ht.1) ht.2.1 d hd
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      have hn := finiteHistoryTrace_all_mem_valid F S w γ (k + 1) σ t ht hσ
      have hυ : MemValid F S υ.1 := hn.2.2.1
      intro d hd
      rw [finiteHistoryTraceGhostDeletions] at hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hBlock _ σ t.1.1 hσ (congrArg Prod.fst ht.1) ht.2.1 d hd
      · exact ih υ t.2.2 ht.2.2.2 hυ d hd

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
