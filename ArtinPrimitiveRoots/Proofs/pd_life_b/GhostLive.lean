import ArtinPrimitiveRoots.Proofs.pd_life_b.GhostFinite

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- Active and pending prime values of one group. -/
def groupLivePrimes {x : ℝ} {K : ℕ} (s : MemPoint x K) (i : Fin K) : List ℕ :=
  List.ofFn (s.2.1 i) ++ (s.2.2 i).map Prod.fst

/-- Live primes are distinct within their group and occur in the birth log. -/
def LiveLogValid {x : ℝ} {K : ℕ} (σ : LogPoint x K) : Prop :=
  (∀ i, (groupLivePrimes σ.1 i).Nodup) ∧
    ∀ i p, p ∈ groupLivePrimes σ.1 i → p ∈ σ.2.map Prod.snd

/-- Canonical ghost births preserve the live-prime invariant whenever their output log
has distinct prime values. Arbitrary deletion subsets are allowed. -/
theorem subsetGhostPoint_live_log_valid {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℕ) (σ : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (σ.1.2.2 i).length))
    (T : (i : Fin K) → (primeBand S.x (F.a i)).powerset)
    (hσ : LiveLogValid σ)
    (hlog : ((subsetGhostPoint F S j σ D T).2.map Prod.snd).Nodup) :
    LiveLogValid (subsetGhostPoint F S j σ D T) := by
  classical
  have hRemove (l : List Particle) (E : Finset (Fin l.length)) :
      List.Sublist (removeIndices l E) l := by
    let p : Fin l.length → Bool := fun k => decide (k ∉ E)
    have hFilter : removeIndices l E = ((List.finRange l.length).filter p).map l.get := by
      unfold removeIndices
      rw [← List.filterMap_eq_map, List.filterMap_filter]
      apply congrArg (fun q => (List.finRange l.length).filterMap q)
      funext k
      by_cases hk : k ∈ E <;> simp [p, hk]
    rw [hFilter]
    have hsub := (List.filter_sublist (p := p) (l := List.finRange l.length)).map l.get
    simpa only [← List.ofFn_eq_map, List.ofFn_get] using hsub
  let R (i : Fin K) := List.ofFn (σ.1.2.1 i) ++
    (removeIndices (σ.1.2.2 i) (D i)).map Prod.fst
  have hRetain (i : Fin K) : List.Sublist (R i) (groupLivePrimes σ.1 i) :=
    ((hRemove _ (D i)).map Prod.fst).append_left _
  have hLive (i : Fin K) :
      groupLivePrimes (subsetGhostPoint F S j σ D T).1 i = R i ++ (T i).1.toList := by
    simp only [groupLivePrimes, subsetGhostPoint, List.map_append, List.map_map,
      Function.comp_def, anchorAt, List.map_id_fun', id_eq, R, List.append_assoc]
  have hLog :
      (subsetGhostPoint F S j σ D T).2.map Prod.snd =
        σ.2.map Prod.snd ++ (List.finRange K).flatMap (fun i => (T i).1.toList) := by
    simp only [subsetGhostPoint, List.map_append, List.map_flatMap, List.map_map]
    congr 1
    apply congrArg (List.finRange K).flatMap
    funext i
    change (T i).1.toList.zipIdx.map Prod.fst = (T i).1.toList
    exact List.zipIdx_map_fst 0 _
  have hTmem (i : Fin K) (p : ℕ) (hp : p ∈ (T i).1.toList) :
      p ∈ (List.finRange K).flatMap (fun i => (T i).1.toList) :=
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hp⟩
  rw [hLog] at hlog
  have hFresh := List.disjoint_of_nodup_append hlog
  constructor
  · intro i
    rw [hLive i]
    apply List.Nodup.append
    · exact (hRetain i).nodup (hσ.1 i)
    · exact (T i).1.nodup_toList
    · apply List.disjoint_left.mpr
      intro p hR hT
      exact List.disjoint_left.mp hFresh
        (hσ.2 i p ((hRetain i).subset hR)) (hTmem i p hT)
  · intro i p hp
    rw [hLive i] at hp
    rw [hLog]
    rcases List.mem_append.mp hp with hR | hT
    · exact List.mem_append.mpr (Or.inl (hσ.2 i p ((hRetain i).subset hR)))
    · exact List.mem_append.mpr (Or.inr (hTmem i p hT))

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
