import ArtinPrimitiveRoots.Proofs.pd_life_b.AllTraceAbsent

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- A valid trace deletes each prime at most once in each group. -/
theorem finiteHistoryTrace_ghost_deletions_nodup_group_prime {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t)
    (hσ : LiveLogValid σ) :
    ((finiteHistoryTraceGhostDeletions F S γ k σ t).map
      (fun d => (d.2.1, d.2.2.1))).Nodup := by
  classical
  let block (ω : LogPoint S.x K)
      (D : (i : Fin K) → Finset (Fin (ω.1.2.2 i).length)) :=
    (List.finRange K).flatMap fun i =>
      (D i).toList.map fun r => (i, ((ω.1.2.2 i).get r).1)
  have hMapBlock (v : Fin (pathLength S.x + 1)) (ω : LogPoint S.x K)
      (D : (i : Fin K) → Finset (Fin (ω.1.2.2 i).length)) :
      (((List.finRange K).flatMap fun i =>
        (D i).toList.map fun r => (v, i, (ω.1.2.2 i).get r)).map
          (fun d => (d.2.1, d.2.2.1))) = block ω D := by
    rw [List.map_flatMap]
    apply congrArg (List.finRange K).flatMap
    funext i
    rw [List.map_map]
    rfl
  have hBlockNodup (ω : LogPoint S.x K)
      (D : (i : Fin K) → Finset (Fin (ω.1.2.2 i).length))
      (hω : LiveLogValid ω) : (block ω D).Nodup := by
    apply List.nodup_flatMap.mpr
    constructor
    · intro i _
      have hn := (List.nodup_append.mp (hω.1 i)).2.1
      obtain ⟨e, he⟩ := memory_prime_index_equiv (ω.1.2.2 i) hn
      apply List.Nodup.map _ (D i).nodup_toList
      intro r s hrs
      apply e.injective
      apply Subtype.ext
      rw [he r, he s]
      exact congrArg Prod.snd hrs
    · apply (List.nodup_finRange K).imp
      intro i i' hne
      apply List.disjoint_left.mpr
      intro a ha ha'
      rcases List.mem_map.mp ha with ⟨r, _, hr⟩
      rcases List.mem_map.mp ha' with ⟨r', _, hr'⟩
      exact hne ((congrArg Prod.fst hr).trans (congrArg Prod.fst hr').symm)
  have hBlockAbsent (ω : LogPoint S.x K)
      (D : (i : Fin K) → Finset (Fin (ω.1.2.2 i).length))
      (i : Fin K) (p : ℕ) (h : p ∉ groupLivePrimes ω.1 i) :
      (i, p) ∉ block ω D := by
    intro hp
    rcases List.mem_flatMap.mp hp with ⟨a, _, ha⟩
    rcases List.mem_map.mp ha with ⟨r, _, hr⟩
    have hi : a = i := congrArg Prod.fst hr
    have hp' : ((ω.1.2.2 a).get r).1 = p := congrArg Prod.snd hr
    subst a
    exact h (List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨(ω.1.2.2 i).get r, List.get_mem _ r, hp'⟩)))
  have hNoDelete (i : Fin K) (p : ℕ) :
      ∀ (m : ℕ) (ω : LogPoint S.x K) (q : FiniteHistoryTrace F S γ m ω),
        FiniteHistoryTraceAll F S γ (fun υ => p ∉ groupLivePrimes υ.1 i) m ω q →
          (i, p) ∉ ((finiteHistoryTraceGhostDeletions F S γ m ω q).map
            (fun d => (d.2.1, d.2.2.1))) := by
    intro m
    induction m with
    | zero =>
        intro ω q h
        rw [finiteHistoryTraceGhostDeletions, hMapBlock]
        exact hBlockAbsent ω q.1 i p h.1
    | succ m ih =>
        intro ω q h
        rw [finiteHistoryTraceGhostDeletions, List.map_append, hMapBlock]
        intro hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hBlockAbsent ω q.1.1 i p h.1 hp
        · exact ih _ q.2.2 h.2.2.2 hp
  have hPerm (ω : LogPoint S.x K)
      (π : Fin K → Equiv.Perm (Fin (slotCount S.x))) (i : Fin K) (p : ℕ)
      (h : p ∉ groupLivePrimes ω.1 i) :
      p ∉ groupLivePrimes (permuteLogPoint π ω).1 i := by
    have hList : (groupLivePrimes (permuteLogPoint π ω).1 i).Perm
        (groupLivePrimes ω.1 i) := by
      change (List.ofFn (ω.1.2.1 i ∘ π i) ++ (ω.1.2.2 i).map Prod.fst).Perm
        (List.ofFn (ω.1.2.1 i) ++ (ω.1.2.2 i).map Prod.fst)
      exact ((π i).ofFn_comp_perm (ω.1.2.1 i)).append_right _
    exact fun hp => h (hList.mem_iff.mp hp)
  have hGhostLog (j : ℕ) (ω : LogPoint S.x K) (g : GhostTraceChoice F S ω)
      (p : ℕ) (hp : p ∈ ω.2.map Prod.snd) :
      p ∈ (ghostTraceOutput F S j ω g).2.map Prod.snd := by
    change p ∈ (ω.2 ++ _).map Prod.snd
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inl hp)
  have hEdgeLog (j : ℕ) (z' : ℤ × ℤ) (ω : LogPoint S.x K)
      (e : EdgeTraceChoice F S ω) (p : ℕ) (hp : p ∈ ω.2.map Prod.snd) :
      p ∈ (edgeTraceOutput F S j z' ω e).2.map Prod.snd := by
    change p ∈ (ω.2 ++ _).map Prod.snd
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inl hp)
  induction k generalizing σ with
  | zero =>
      rw [finiteHistoryTraceGhostDeletions, hMapBlock]
      exact hBlockNodup σ t.1 hσ
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let ω := edgeOutputPoint F S j (permuteLogPoint t.2.1.1 τ) t.2.1.2.1 z'
      let υ := edgeTraceOutput F S j z' τ t.2.1
      have hn := finiteHistoryTrace_all_log_nodup F S w γ (k + 1) σ t ht
      have hl := finiteHistoryTrace_all_live_log_valid F S w γ (k + 1) σ t ht hσ
      have hτ : LiveLogValid τ := hl.2.1
      have hυ : LiveLogValid υ := hl.2.2.1
      rw [finiteHistoryTraceGhostDeletions, List.map_append, hMapBlock]
      apply List.Nodup.append (hBlockNodup σ t.1.1 hσ)
        (ih υ t.2.2 ht.2.2.2 hυ)
      apply List.disjoint_left.mpr
      intro a ha hb
      rcases List.mem_flatMap.mp ha with ⟨i, _, hi⟩
      rcases List.mem_map.mp hi with ⟨r, hr, rfl⟩
      let p := ((σ.1.2.2 i).get r).1
      have hpLog : p ∈ σ.2.map Prod.snd := hσ.2 i p
        (List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨(σ.1.2.2 i).get r, List.get_mem _ r, rfl⟩)))
      have hpτLog : p ∈ τ.2.map Prod.snd := hGhostLog j σ t.1 p hpLog
      have hpτ : p ∉ groupLivePrimes τ.1 i :=
        subsetGhostPoint_deleted_prime_absent F S j σ t.1.1 t.1.2 hσ hn.2.1
          i r (Finset.mem_toList.mp hr)
      have hpω : p ∉ groupLivePrimes ω.1 i :=
        edgeOutputPoint_prime_absent_of_logged F S j (permuteLogPoint t.2.1.1 τ)
          t.2.1.2.1 z' (permuteLists_live_log_valid τ t.2.1.1 hτ)
          hn.2.2.1 i p hpτLog (hPerm τ t.2.1.1 i p hpτ)
      have hpυ : p ∉ groupLivePrimes υ.1 i := hPerm ω t.2.1.2.2 i p hpω
      have hpυLog : p ∈ υ.2.map Prod.snd := hEdgeLog j z' τ t.2.1 p hpτLog
      exact hNoDelete i p k υ t.2.2
        (finiteHistoryTrace_all_prime_absent_of_logged F S w γ k υ t.2.2
          ht.2.2.2 hυ i p hpυLog hpυ) hb

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
