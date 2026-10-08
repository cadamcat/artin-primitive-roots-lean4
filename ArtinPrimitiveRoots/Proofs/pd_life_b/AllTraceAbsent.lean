import ArtinPrimitiveRoots.Proofs.pd_life_b.EdgeAbsentPreservation

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- An absent source-logged prime stays absent at every state of a valid trace. -/
theorem finiteHistoryTrace_all_prime_absent_of_logged {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t)
    (hσ : LiveLogValid σ) (i : Fin K) (p : ℕ)
    (hpLog : p ∈ σ.2.map Prod.snd)
    (hpAbsent : p ∉ groupLivePrimes σ.1 i) :
    FiniteHistoryTraceAll F S γ
      (fun υ => p ∉ groupLivePrimes υ.1 i) k σ t := by
  have hPerm (ω : LogPoint S.x K)
      (π : Fin K → Equiv.Perm (Fin (slotCount S.x)))
      (h : p ∉ groupLivePrimes ω.1 i) :
      p ∉ groupLivePrimes (permuteLogPoint π ω).1 i := by
    have hList : (groupLivePrimes (permuteLogPoint π ω).1 i).Perm
        (groupLivePrimes ω.1 i) := by
      change (List.ofFn (ω.1.2.1 i ∘ π i) ++ (ω.1.2.2 i).map Prod.fst).Perm
        (List.ofFn (ω.1.2.1 i) ++ (ω.1.2.2 i).map Prod.fst)
      exact ((π i).ofFn_comp_perm (ω.1.2.1 i)).append_right _
    exact fun hp => h (hList.mem_iff.mp hp)
  have hGhostLog (j : ℕ) (ω : LogPoint S.x K) (g : GhostTraceChoice F S ω)
      (hp : p ∈ ω.2.map Prod.snd) :
      p ∈ (ghostTraceOutput F S j ω g).2.map Prod.snd := by
    change p ∈ (ω.2 ++ _).map Prod.snd
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inl hp)
  have hEdgeLog (j : ℕ) (z' : ℤ × ℤ) (ω : LogPoint S.x K)
      (e : EdgeTraceChoice F S ω) (hp : p ∈ ω.2.map Prod.snd) :
      p ∈ (edgeTraceOutput F S j z' ω e).2.map Prod.snd := by
    change p ∈ (ω.2 ++ _).map Prod.snd
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inl hp)
  induction k generalizing σ with
  | zero =>
      have hn := finiteHistoryTrace_all_log_nodup F S w γ 0 σ t ht
      exact ⟨hpAbsent, subsetGhostPoint_prime_absent_of_logged F S (pathLength S.x)
        σ t.1 t.2 hσ hn.2 i p hpLog hpAbsent⟩
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
      have hpτLog : p ∈ τ.2.map Prod.snd := hGhostLog j σ t.1 hpLog
      have hpτ : p ∉ groupLivePrimes τ.1 i :=
        subsetGhostPoint_prime_absent_of_logged F S j σ t.1.1 t.1.2
          hσ hn.2.1 i p hpLog hpAbsent
      have hpω : p ∉ groupLivePrimes ω.1 i :=
        edgeOutputPoint_prime_absent_of_logged F S j (permuteLogPoint t.2.1.1 τ)
          t.2.1.2.1 z' (permuteLists_live_log_valid τ t.2.1.1 hτ)
          hn.2.2.1 i p hpτLog (hPerm τ t.2.1.1 hpτ)
      have hpυ : p ∉ groupLivePrimes υ.1 i := hPerm ω t.2.1.2.2 hpω
      have hpυLog : p ∈ υ.2.map Prod.snd := hEdgeLog j z' τ t.2.1 hpτLog
      exact ⟨hpAbsent, hpτ, hpυ, ih υ t.2.2 ht.2.2.2 hυ hpυLog hpυ⟩

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
