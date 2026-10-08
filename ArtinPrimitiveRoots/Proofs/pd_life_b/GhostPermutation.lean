import ArtinPrimitiveRoots.Proofs.pd_life_b.MemoryIndexTransport

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD

/-- Positions and active slots agree; memory particles and logged prime values may be reordered. -/
def LoggedPerm {x : ℝ} {K : ℕ} (σ τ : LogPoint x K) : Prop :=
  σ.1.1 = τ.1.1 ∧ σ.1.2.1 = τ.1.2.1 ∧
    (∀ i, (σ.1.2.2 i).Perm (τ.1.2.2 i)) ∧
    (σ.2.map Prod.snd).Perm (τ.2.map Prod.snd)

def RespectsLoggedPerm {x : ℝ} {K : ℕ} (f : LogPoint x K → ℂ) : Prop :=
  ∀ σ τ, LoggedPerm σ τ → f σ = f τ

/-- Ghost deletion choices transport along memory index permutations. -/
theorem logGhost_respects_perm {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (f : LogPoint S.x K → ℂ)
    (hf : RespectsLoggedPerm f) :
    RespectsLoggedPerm (logGhost F S ρ j f) := by
  classical
  rintro ⟨s, L⟩ ⟨t, M⟩ ⟨hz, hp, hmemory, hlog⟩
  have hex (i : Fin K) := perm_index_equiv (s.2.2 i) (t.2.2 i) (hmemory i)
  choose e he using hex
  let E : ((i : Fin K) → Finset (Fin (s.2.2 i).length)) ≃
      ((i : Fin K) → Finset (Fin (t.2.2 i).length)) :=
    Equiv.piCongrRight fun i => Equiv.finsetCongr (e i)
  have hHits (i : Fin K) :
      (hitIndices (s.2.2 i) s.1).map (e i).toEmbedding =
        hitIndices (t.2.2 i) t.1 := by
    rw [← hz]
    exact (memory_index_transport _ _ _ (e i) (he i) ∅).1
  have hCount (i : Fin K) : hitCount (s.2.2 i) s.1 = hitCount (t.2.2 i) t.1 := by
    unfold hitCount
    rw [← hHits i, Finset.card_map]
  have hGuard (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) :
      (∀ i, D i ⊆ hitIndices (s.2.2 i) s.1) ↔
        (∀ i, (E D) i ⊆ hitIndices (t.2.2 i) t.1) := by
    have hi (i : Fin K) :
        D i ⊆ hitIndices (s.2.2 i) s.1 ↔
          (E D) i ⊆ hitIndices (t.2.2 i) t.1 := by
      change _ ↔ (D i).map (e i).toEmbedding ⊆ _
      rw [← hHits i, Finset.map_subset_map]
    exact forall_congr' hi
  unfold logGhost
  dsimp only
  refine Fintype.sum_equiv E _ _ ?_
  intro D
  apply tsum_congr
  intro l
  apply Finset.sum_congr rfl
  intro new _
  by_cases hd : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1
  · rw [if_pos hd, if_pos ((hGuard D).mp hd)]
    have hCoeff :
        (∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1)
          (D i).card (l i) (List.ofFn fun k => (new i k : ℕ))) =
        (∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (t.2.2 i) t.1)
          ((E D) i).card (l i) (List.ofFn fun k => (new i k : ℕ))) := by
      apply Finset.prod_congr rfl
      intro i _
      have hCard : ((E D) i).card = (D i).card := Finset.card_map _
      rw [hCount i, hCard]
    rw [hCoeff]
    congr 1
    apply hf
    refine ⟨hz, hp, ?_, ?_⟩
    · intro i
      have hSurv := (memory_index_transport _ _ s.1 (e i) (he i) (D i)).2.2
      change (removeIndices (s.2.2 i) (D i) ++ _).Perm
        (removeIndices (t.2.2 i) ((D i).map (e i).toEmbedding) ++ _)
      rw [hz]
      exact hSurv.append_right _
    · simp only [List.map_append]
      exact hlog.append_right _
  · rw [if_neg hd, if_neg (fun h => hd ((hGuard D).mpr h))]

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
