import ArtinPrimitiveRoots.Proofs.pd_life_b.AllTraceLive

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- Valid traces preserve primitive positions, band membership, and legal particle anchors. -/
theorem finiteHistoryTrace_all_mem_valid {K : ℕ}
    (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (k : ℕ) (σ : LogPoint S.x K) (t : FiniteHistoryTrace F S γ k σ)
    (ht : FiniteHistoryTraceValid F S w γ k σ t)
    (hσ : MemValid F S σ.1) :
    FiniteHistoryTraceAll F S γ (fun τ => MemValid F S τ.1) k σ t := by
  classical
  have hRemove (l : List Particle) (D : Finset (Fin l.length))
      (e : Particle) (he : e ∈ removeIndices l D) : e ∈ l := by
    unfold removeIndices at he
    rcases List.mem_filterMap.mp he with ⟨m, _, hm⟩
    by_cases hd : m ∈ D
    · simp only [hd, ite_true] at hm
      cases hm
    · have heq : l.get m = e := by
        simpa only [hd, ite_false, Option.some.injEq] using hm
      rw [← heq]
      exact List.get_mem l m
  have hAnchor (p : ℕ) (z : ℤ × ℤ) :
      (anchorAt p z).2 ≤ (anchorAt p z).1 :=
    Nat.le_of_lt_succ (projLine p z).isLt
  have hPerm (τ : LogPoint S.x K)
      (π : Fin K → Equiv.Perm (Fin (slotCount S.x)))
      (hv : MemValid F S τ.1) : MemValid F S (permuteLogPoint π τ).1 := by
    exact ⟨hv.1, fun i m => hv.2.1 i (π i m), hv.2.2⟩
  have hGhost (j : ℕ) (τ : LogPoint S.x K) (g : GhostTraceChoice F S τ)
      (hv : MemValid F S τ.1) : MemValid F S (ghostTraceOutput F S j τ g).1 := by
    refine ⟨hv.1, hv.2.1, ?_⟩
    intro i e he
    change e ∈ removeIndices (τ.1.2.2 i) (g.1 i) ++
      ((g.2 i).1.toList.map fun p => anchorAt p τ.1.1) at he
    rcases List.mem_append.mp he with he | he
    · exact hv.2.2 i e (hRemove _ _ e he)
    · rcases List.mem_map.mp he with ⟨p, hp, rfl⟩
      exact ⟨(Finset.mem_powerset.mp (g.2 i).2) (Finset.mem_toList.mp hp),
        hAnchor p τ.1.1⟩
  have hEdge (j : ℕ) (z' : ℤ × ℤ) (τ : LogPoint S.x K)
      (e : EdgeTraceChoice F S τ) (hv : MemValid F S τ.1)
      (ha : EdgeAdmissible F S w (permuteLogPoint e.1 τ).1 e.2.1 z') :
      MemValid F S (edgeTraceOutput F S j z' τ e).1 := by
    let πτ := permuteLogPoint e.1 τ
    let c := e.2.1
    let ω := edgeOutputPoint F S j πτ c z'
    have hπτ := hPerm τ e.1 hv
    have hω : MemValid F S ω.1 := by
      refine ⟨ha.2.2.2.2.2.1, fun i m => (ha.2.2.1.1 i m).2, ?_⟩
      intro i b hb
      change b ∈ edgeNewMemory F S πτ.1 c i at hb
      unfold edgeNewMemory at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hπτ.2.2 i b (hRemove _ _ b hb)
      · by_cases hs : (c i).1 = true
        · rw [ite_eq_left hs] at hb
          have hb' := List.mem_singleton.mp hb
          subst b
          exact ⟨(ha.2.1.1 i (lastSlot S.x)).2,
            hAnchor (πτ.1.2.1 i (lastSlot S.x)) πτ.1.1⟩
        · rw [ite_eq_right hs] at hb
          cases hb
    exact hPerm ω e.2.2 hω
  induction k generalizing σ with
  | zero => exact ⟨hσ, hGhost (pathLength S.x) σ t hσ⟩
  | succ k ih =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      have hτ := hGhost j σ t.1 hσ
      have hυ := hEdge j z' τ t.2.1 hτ ht.2.2.1
      exact ⟨hσ, hτ, hυ, ih υ t.2.2 ht.2.2.2 hυ⟩

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
