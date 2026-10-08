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

/-- Each prime in the deletion list has a unique event carrying it. -/
theorem finiteHistoryTrace_ghost_deletion_existsUnique_of_mem_prime {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t)
    (hσ : LiveLogValid σ) (hMem : MemValid F S σ.1)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (p : ℕ)
    (hp : p ∈ (finiteHistoryTraceGhostDeletions F S γ k σ t).map
      (fun d => d.2.2.1)) :
    ∃! d : Fin (pathLength S.x + 1) × Fin K × Particle,
      d ∈ finiteHistoryTraceGhostDeletions F S γ k σ t ∧ d.2.2.1 = p := by
  rcases List.mem_map.mp hp with ⟨d, hd, rfl⟩
  refine ⟨d, ⟨hd, rfl⟩, ?_⟩
  intro e he
  exact finiteHistoryTrace_ghost_deletion_eq_of_prime_eq F S w γ k σ t ht hσ
    hMem hBands he.1 hd he.2

/-- Equal-prime ghost births are the same recorded event. -/
theorem finiteHistoryTrace_ghost_birth_eq_of_prime_eq {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t)
    {b b' : Fin (pathLength S.x + 1) × Fin K × ℕ}
    (hb : b ∈ finiteHistoryTraceGhostBirths F S γ k σ t)
    (hb' : b' ∈ finiteHistoryTraceGhostBirths F S γ k σ t)
    (hprime : b.2.2 = b'.2.2) : b = b' := by
  let G := finiteHistoryTraceGhostBirths F S γ k σ t
  have hPrime : (G.map fun b => b.2.2).Nodup := by
    simpa [G] using
      (finiteHistoryTrace_ghost_birth_data F S w γ k σ t ht).1
  have hG : G.Nodup := hPrime.of_map
  have hInj := (List.nodup_map_iff_inj_on hG).1 hPrime
  exact hInj b (by simpa [G] using hb) b' (by simpa [G] using hb') hprime

/-- Each prime in the birth list has a unique event carrying it. -/
theorem finiteHistoryTrace_ghost_birth_existsUnique_of_mem_prime {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t)
    (p : ℕ)
    (hp : p ∈ (finiteHistoryTraceGhostBirths F S γ k σ t).map
      (fun b => b.2.2)) :
    ∃! b : Fin (pathLength S.x + 1) × Fin K × ℕ,
      b ∈ finiteHistoryTraceGhostBirths F S γ k σ t ∧ b.2.2 = p := by
  rcases List.mem_map.mp hp with ⟨b, hb, rfl⟩
  refine ⟨b, ⟨hb, rfl⟩, ?_⟩
  intro b' hb'
  exact finiteHistoryTrace_ghost_birth_eq_of_prime_eq F S w γ k σ t ht
    hb'.1 hb hb'.2

/-- Every recorded ghost birth occurs at or after the first visit of its trace suffix. -/
theorem finiteHistoryTrace_ghost_births_visit_lower_bound {K : ℕ}
    (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K)
    (t : FiniteHistoryTrace F S γ k σ) :
    ∀ b ∈ finiteHistoryTraceGhostBirths F S γ k σ t,
      pathLength S.x - k ≤ b.1.val := by
  induction k generalizing σ with
  | zero =>
      intro b hb
      rw [finiteHistoryTraceGhostBirths] at hb
      rcases List.mem_flatMap.mp hb with ⟨i, hi, hbi⟩
      rcases List.mem_map.mp hbi with ⟨p, hp, rfl⟩
      simp
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      intro b hb
      rw [finiteHistoryTraceGhostBirths] at hb
      rcases List.mem_append.mp hb with hb | hb
      · rcases List.mem_flatMap.mp hb with ⟨i, hi, hbi⟩
        rcases List.mem_map.mp hbi with ⟨p, hp, rfl⟩
        dsimp only [j]
        exact le_rfl
      · have hTail := ih υ t.2.2 b hb
        omega

/-- Ghost-birth events are listed in nondecreasing visit order. -/
theorem finiteHistoryTrace_ghost_births_visit_monotone {K : ℕ}
    (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K)
    (t : FiniteHistoryTrace F S γ k σ) :
    List.Pairwise (fun b b' => b.1.val ≤ b'.1.val)
      (finiteHistoryTraceGhostBirths F S γ k σ t) := by
  induction k generalizing σ with
  | zero =>
      rw [finiteHistoryTraceGhostBirths]
      apply List.pairwise_of_forall_mem_list
      intro b hb b' hb'
      rcases List.mem_flatMap.mp hb with ⟨i, hi, hbi⟩
      rcases List.mem_map.mp hbi with ⟨p, hp, rfl⟩
      rcases List.mem_flatMap.mp hb' with ⟨i', hi', hbi'⟩
      rcases List.mem_map.mp hbi' with ⟨p', hp', rfl⟩
      exact le_rfl
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      have hBlock : List.Pairwise (fun b b' => b.1.val ≤ b'.1.val)
          ((List.finRange K).flatMap fun i =>
            (t.1.2 i).1.toList.map fun p =>
              ((⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ :
                Fin (pathLength S.x + 1)), i, p)) := by
        apply List.pairwise_of_forall_mem_list
        intro b hb b' hb'
        rcases List.mem_flatMap.mp hb with ⟨i, hi, hbi⟩
        rcases List.mem_map.mp hbi with ⟨p, hp, rfl⟩
        rcases List.mem_flatMap.mp hb' with ⟨i', hi', hbi'⟩
        rcases List.mem_map.mp hbi' with ⟨p', hp', rfl⟩
        exact le_rfl
      have hCross : ∀ b ∈ (List.finRange K).flatMap (fun i =>
          (t.1.2 i).1.toList.map fun p =>
            ((⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ :
              Fin (pathLength S.x + 1)), i, p)),
          ∀ b' ∈ finiteHistoryTraceGhostBirths F S γ k υ t.2.2,
            b.1.val ≤ b'.1.val := by
        intro b hb b' hb'
        rcases List.mem_flatMap.mp hb with ⟨i, hi, hbi⟩
        rcases List.mem_map.mp hbi with ⟨p, hp, rfl⟩
        have hLater := finiteHistoryTrace_ghost_births_visit_lower_bound
          F S γ k υ t.2.2 b' hb'
        dsimp only [j]
        omega
      rw [finiteHistoryTraceGhostBirths, List.pairwise_append]
      exact ⟨hBlock, ih υ t.2.2, hCross⟩

/-- Every recorded ghost deletion occurs at or after the first visit of its trace suffix. -/
theorem finiteHistoryTrace_ghost_deletions_visit_lower_bound {K : ℕ}
    (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K)
    (t : FiniteHistoryTrace F S γ k σ) :
    ∀ d ∈ finiteHistoryTraceGhostDeletions F S γ k σ t,
      pathLength S.x - k ≤ d.1.val := by
  induction k generalizing σ with
  | zero =>
      intro d hd
      rw [finiteHistoryTraceGhostDeletions] at hd
      rcases List.mem_flatMap.mp hd with ⟨i, hi, hdi⟩
      rcases List.mem_map.mp hdi with ⟨r, hr, rfl⟩
      simp
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      intro d hd
      rw [finiteHistoryTraceGhostDeletions] at hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_flatMap.mp hd with ⟨i, hi, hdi⟩
        rcases List.mem_map.mp hdi with ⟨r, hr, rfl⟩
        dsimp only [j]
        exact le_rfl
      · have hTail := ih υ t.2.2 d hd
        omega

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
