import ArtinPrimitiveRoots.Proofs.pd_life_b.GhostPermutation

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

/-- Reordering memory particles transports promotion choices without changing an edge piece. -/
theorem logEdgePiece_respects_perm {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (raw : Bool)
    (St Pr : Finset (Fin K)) (f : LogPoint S.x K → ℂ)
    (hf : RespectsLoggedPerm f) :
    RespectsLoggedPerm (logEdgePiece F S ρ w step raw St Pr f) := by
  classical
  rintro ⟨s, L⟩ ⟨t, M⟩ ⟨hz, hp, hmemory, hlog⟩
  change s.1 = t.1 at hz
  change s.2.1 = t.2.1 at hp
  have hex (i : Fin K) := perm_index_equiv (s.2.2 i) (t.2.2 i) (hmemory i)
  choose e he using hex
  let E : ((i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) ≃
      ((i : Fin K) → EdgeChoice S.x F.a (t.2.2 i) i) :=
    Equiv.piCongrRight fun i =>
      Equiv.prodCongr (Equiv.refl Bool) (Equiv.sumCongr (e i) (Equiv.refl _))
  have hLabel (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
      edgeNewLabel (l := s.2.2 i) (c i) =
        edgeNewLabel (l := t.2.2 i) ((E c) i) := by
    rcases hc : c i with ⟨b, k | p⟩
    · simp [edgeNewLabel, E, Equiv.piCongrRight, Equiv.prodCongr, Equiv.sumCongr, hc]
      simpa only [List.get_eq_getElem] using congrArg Prod.fst (he i k)
    · simp [edgeNewLabel, E, Equiv.piCongrRight, Equiv.prodCongr, Equiv.sumCongr, hc]
  have hTarget (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :
      edgeTargetLists F S s c = edgeTargetLists F S t (E c) := by
    funext i jj
    simp only [edgeTargetLists, hp, hLabel c i]
  have hStored (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :
      edgeStoredSet c = edgeStoredSet (E c) := rfl
  have hPromoted (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :
      edgePromotedSet c = edgePromotedSet (E c) := by
    apply Finset.ext
    intro i
    simp only [edgePromotedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    change (c i).2.isLeft = true ↔ (Sum.map (e i) id (c i).2).isLeft = true
    cases (c i).2 <;> rfl
  have hBirths (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :
      edgeBirths F S step s c = edgeBirths F S step t (E c) := by
    unfold edgeBirths
    apply congrArg (List.finRange K).flatMap
    funext i
    change (match (c i).2 with
      | Sum.inl _ => []
      | Sum.inr p => [(BirthAddress.edge step i, (p : ℕ))]) =
      (match Sum.map (e i) id (c i).2 with
      | Sum.inl _ => []
      | Sum.inr p => [(BirthAddress.edge step i, (p : ℕ))])
    cases (c i).2 <;> rfl
  have hMemory (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
      (edgeNewMemory F S s c i).Perm (edgeNewMemory F S t (E c) i) := by
    have hRemove :
        (removeIndices (s.2.2 i) (match (c i).2 with
          | Sum.inl k => {k}
          | Sum.inr _ => ∅)).Perm
        (removeIndices (t.2.2 i) (match Sum.map (e i) id (c i).2 with
          | Sum.inl k => {k}
          | Sum.inr _ => ∅)) := by
      cases hc : (c i).2 with
      | inl k =>
          simpa only [hc, Sum.map_inl, Finset.map_singleton, Equiv.toEmbedding_apply] using
            (memory_index_transport _ _ s.1 (e i) (he i) {k}).2.2
      | inr p =>
          simpa only [hc, Sum.map_inr, Finset.map_empty] using
            (memory_index_transport _ _ s.1 (e i) (he i) ∅).2.2
    change (removeIndices (s.2.2 i) _ ++
      (if (c i).1 then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else [])).Perm
      (removeIndices (t.2.2 i) _ ++
      (if (c i).1 then [anchorAt (t.2.1 i (lastSlot S.x)) t.1] else []))
    rw [← hp, ← hz]
    exact hRemove.append_right _
  have hPromotionGuard (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
      (z' : ℤ × ℤ) :
      (∀ i k, (c i).2 = Sum.inl k → particleHits ((s.2.2 i).get k) z') ↔
        (∀ i k, ((E c) i).2 = Sum.inl k → particleHits ((t.2.2 i).get k) z') := by
    constructor
    · intro h i k hc
      rcases (e i).surjective k with ⟨k₀, rfl⟩
      have hc₀ : (c i).2 = Sum.inl k₀ := by
        apply (Equiv.sumCongr (e i) (Equiv.refl _)).injective
        exact hc
      simpa only [he i k₀] using h i k₀ hc₀
    · intro h i k hc
      have hc' : ((E c) i).2 = Sum.inl ((e i) k) := by
        change Sum.map (e i) id (c i).2 = _
        rw [hc]
        rfl
      rw [he i k]
      exact h i ((e i) k) hc'
  have hAdmissible (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
      (z' : ℤ × ℤ) :
      EdgeAdmissible F S w s c z' ↔ EdgeAdmissible F S w t (E c) z' := by
    unfold EdgeAdmissible
    rw [hPromotionGuard c z', hp, hz, hTarget c]
  have hOldCount (i : Fin K) : hitCount (s.2.2 i) s.1 = hitCount (t.2.2 i) t.1 := by
    rw [← hz]
    exact (memory_index_transport _ _ s.1 (e i) (he i) ∅).2.1
  have hNewCount (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
      (z' : ℤ × ℤ) (i : Fin K) :
      hitCount (edgeNewMemory F S s c i) z' =
        hitCount (edgeNewMemory F S t (E c) i) z' := by
    obtain ⟨e', he'⟩ := perm_index_equiv _ _ (hMemory c i)
    exact (memory_index_transport _ _ z' e' he' ∅).2.1
  unfold logEdgePiece
  dsimp only
  refine Fintype.sum_equiv E _ _ ?_
  intro c
  apply tsum_congr
  intro z'
  have hGuard :
      (edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c z') ↔
      (edgeStoredSet (E c) = St ∧ edgePromotedSet (E c) = Pr ∧
        EdgeAdmissible F S w t (E c) z') := by
    rw [hStored c, hPromoted c, hAdmissible c z']
  by_cases hc : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
      EdgeAdmissible F S w s c z'
  · rw [ite_eq_left hc, ite_eq_left (hGuard.mp hc)]
    have hCont :
        f ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
          L ++ edgeBirths F S step s c) =
        f ((z', edgeTargetLists F S t (E c), edgeNewMemory F S t (E c)),
          M ++ edgeBirths F S step t (E c)) := by
      apply hf
      refine ⟨rfl, hTarget c, hMemory c, ?_⟩
      simp only [List.map_append, hBirths c]
      exact hlog.append_right _
    simp only [hOldCount, hNewCount c z']
    rw [hCont, hp, hz, hTarget c]
    congr 5
    apply Finset.prod_congr rfl
    intro i _
    rcases hi : c i with ⟨b, k | p⟩ <;>
      simp [E, Equiv.piCongrRight, Equiv.prodCongr, Equiv.sumCongr, hi]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hGuard.mpr h))]

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
