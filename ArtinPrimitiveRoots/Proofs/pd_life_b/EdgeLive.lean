import ArtinPrimitiveRoots.Proofs.pd_life_b.GhostLive

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- The logged output of one edge choice. -/
def edgeOutputPoint {K : ℕ} (F : PDFix K) (S : PDScale) (step : ℕ)
    (σ : LogPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (σ.1.2.2 i) i)
    (z' : ℤ × ℤ) : LogPoint S.x K :=
  ((z', edgeTargetLists F S σ.1 c, edgeNewMemory F S σ.1 c),
    σ.2 ++ edgeBirths F S step σ.1 c)

private theorem removeIndices_sublist (l : List Particle)
    (D : Finset (Fin l.length)) : List.Sublist (removeIndices l D) l := by
  classical
  let p : Fin l.length → Bool := fun k => decide (k ∉ D)
  have hFilter : removeIndices l D = ((List.finRange l.length).filter p).map l.get := by
    unfold removeIndices
    rw [← List.filterMap_eq_map, List.filterMap_filter]
    apply congrArg (fun q => (List.finRange l.length).filterMap q)
    funext k
    by_cases hk : k ∈ D <;> simp [p, hk]
  rw [hFilter]
  have hsub := (List.filter_sublist (p := p) (l := List.finRange l.length)).map l.get
  simpa only [← List.ofFn_eq_map, List.ofFn_get] using hsub

private theorem mem_removeIndices {l : List Particle}
    {D : Finset (Fin l.length)} {e : Particle} (he : e ∈ removeIndices l D) :
    ∃ k : Fin l.length, k ∉ D ∧ l.get k = e := by
  classical
  rcases List.mem_filterMap.mp he with ⟨k, _, hk⟩
  by_cases hd : k ∈ D
  · simp [hd] at hk
  · exact ⟨k, hd, by simpa [hd] using hk⟩

/-- Admissible edge choices preserve distinct live values and their birth-log membership. -/
theorem edgeOutputPoint_live_log_valid {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (step : ℕ) (σ : LogPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (σ.1.2.2 i) i)
    (z' : ℤ × ℤ) (hσ : LiveLogValid σ)
    (hEdge : EdgeAdmissible F S w σ.1 c z')
    (hlog : ((edgeOutputPoint F S step σ c z').2.map Prod.snd).Nodup) :
    LiveLogValid (edgeOutputPoint F S step σ c z') := by
  classical
  let D (i : Fin K) : Finset (Fin (σ.1.2.2 i).length) :=
    match (c i).2 with
    | Sum.inl k => {k}
    | Sum.inr _ => ∅
  let R (i : Fin K) := (removeIndices (σ.1.2.2 i) (D i)).map Prod.fst
  let A (i : Fin K) := List.ofFn (edgeTargetLists F S σ.1 c i)
  let O (i : Fin K) := if (c i).1 then [σ.1.2.1 i (lastSlot S.x)] else []
  have hLive (i : Fin K) :
      groupLivePrimes (edgeOutputPoint F S step σ c z').1 i = A i ++ R i ++ O i := by
    cases hc : (c i).2 <;> cases hb : (c i).1 <;>
      simp [groupLivePrimes, edgeOutputPoint, edgeNewMemory, A, R, D, O,
        hc, hb, anchorAt, List.append_assoc]
  have hLog : (edgeOutputPoint F S step σ c z').2.map Prod.snd =
      σ.2.map Prod.snd ++ (edgeBirths F S step σ.1 c).map Prod.snd := by
    simp only [edgeOutputPoint, List.map_append]
  rw [hLog] at hlog
  have hFresh := List.disjoint_of_nodup_append hlog
  have hBirth (i : Fin K) (p : primeBand S.x (F.a i))
      (hc : (c i).2 = Sum.inr p) :
      (p : ℕ) ∈ (edgeBirths F S step σ.1 c).map Prod.snd := by
    apply List.mem_map.mpr
    refine ⟨(BirthAddress.edge step i, (p : ℕ)), ?_, rfl⟩
    unfold edgeBirths
    apply List.mem_flatMap.mpr
    exact ⟨i, List.mem_finRange i, by simp [hc]⟩
  have hOldActive (i : Fin K) (j : Fin (slotCount S.x)) :
      σ.1.2.1 i j ∈ groupLivePrimes σ.1 i := by
    exact List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨j, rfl⟩))
  have hOldMemory (i : Fin K) (p : ℕ) (hp : p ∈ (σ.1.2.2 i).map Prod.fst) :
      p ∈ groupLivePrimes σ.1 i := List.mem_append.mpr (Or.inr hp)
  have hRsub (i : Fin K) : List.Sublist (R i) ((σ.1.2.2 i).map Prod.fst) :=
    (removeIndices_sublist _ (D i)).map Prod.fst
  have hRlive (i : Fin K) (p : ℕ) (hp : p ∈ R i) :
      p ∈ groupLivePrimes σ.1 i := hOldMemory i p ((hRsub i).subset hp)
  have hOlive (i : Fin K) (p : ℕ) (hp : p ∈ O i) :
      p ∈ groupLivePrimes σ.1 i := by
    cases hb : (c i).1 <;> simp [O, hb] at hp
    subst p
    exact hOldActive i (lastSlot S.x)
  have hAlabel (i : Fin K) (j : Fin (slotCount S.x))
      (hj : ¬ j.val < momentJ S.x) :
      edgeTargetLists F S σ.1 c i j = edgeNewLabel (c i) := by
    simp only [edgeTargetLists, ite_eq_right hj]
  have hAdisjoint (i : Fin K) : List.Disjoint (A i) (R i) := by
    apply List.disjoint_left.mpr
    intro p hp hR
    rcases List.mem_ofFn.mp hp with ⟨j, rfl⟩
    by_cases hj : j.val < momentJ S.x
    · have hEq : edgeTargetLists F S σ.1 c i j = σ.1.2.1 i j := by
        simp only [edgeTargetLists, ite_eq_left hj]
      rw [hEq] at hR
      exact List.disjoint_left.mp (List.disjoint_of_nodup_append (hσ.1 i))
        (List.mem_ofFn.mpr ⟨j, rfl⟩) ((hRsub i).subset hR)
    · rw [hAlabel i j hj] at hR
      cases hc : (c i).2 with
      | inl k =>
          have hNew : edgeNewLabel (c i) = ((σ.1.2.2 i).get k).1 := by
            simp only [edgeNewLabel, hc]
          rw [hNew] at hR
          rcases List.mem_map.mp hR with ⟨e, he, hp⟩
          rcases mem_removeIndices he with ⟨k', hk', heq⟩
          have hInjective : Function.Injective
              (fun t : Fin (σ.1.2.2 i).length => ((σ.1.2.2 i).get t).1) := by
            apply List.nodup_ofFn.mp
            have hn := (List.nodup_append.mp (hσ.1 i)).2.1
            convert hn using 1
            change List.ofFn (Prod.fst ∘ (σ.1.2.2 i).get) = _
            rw [← List.map_ofFn, List.ofFn_get]
          have hkk : k' = k := hInjective ((congrArg Prod.fst heq).trans hp)
          subst k'
          exact hk' (by simp [D, hc])
      | inr p =>
          have hNew : edgeNewLabel (c i) = (p : ℕ) := by
            simp only [edgeNewLabel, hc]
          rw [hNew] at hR
          exact List.disjoint_left.mp hFresh
            (hσ.2 i p (hRlive i p hR)) (hBirth i p hc)
  have hOdisjoint (i : Fin K) : List.Disjoint (A i ++ R i) (O i) := by
    apply List.disjoint_left.mpr
    intro p hp ho
    cases hb : (c i).1 <;> simp [O, hb] at ho
    subst p
    rcases List.mem_append.mp hp with hA | hR
    · rcases List.mem_ofFn.mp hA with ⟨j, hjEq⟩
      by_cases hj : j.val < momentJ S.x
      · have hEq : edgeTargetLists F S σ.1 c i j = σ.1.2.1 i j := by
          simp only [edgeTargetLists, ite_eq_left hj]
        have hne : j ≠ lastSlot S.x := by
          intro heq
          subst j
          exact Nat.lt_irrefl _ hj
        exact hEdge.2.1.2 i j (lastSlot S.x) hne (hEq.symm.trans hjEq)
      · have hLast : j = lastSlot S.x := by
          apply Fin.ext
          have hlt := j.isLt
          change j.val < momentJ S.x + 1 at hlt
          change j.val = momentJ S.x
          omega
        subst j
        exact hEdge.2.2.2.1.2 i i (lastSlot S.x) hjEq
    · exact List.disjoint_left.mp (List.disjoint_of_nodup_append (hσ.1 i))
        (List.mem_ofFn.mpr ⟨lastSlot S.x, rfl⟩) ((hRsub i).subset hR)
  constructor
  · intro i
    rw [hLive i]
    apply List.Nodup.append
    · apply List.Nodup.append
      · apply List.nodup_ofFn.mpr
        intro j j' heq
        by_contra hne
        exact hEdge.2.2.1.2 i j j' hne heq
      · exact (hRsub i).nodup ((List.nodup_append.mp (hσ.1 i)).2.1)
      · exact hAdisjoint i
    · cases hb : (c i).1 <;> simp [O, hb]
    · exact hOdisjoint i
  · intro i p hp
    rw [hLive i] at hp
    rw [hLog]
    rcases List.mem_append.mp hp with hAR | hO
    · rcases List.mem_append.mp hAR with hA | hR
      · rcases List.mem_ofFn.mp hA with ⟨j, rfl⟩
        by_cases hj : j.val < momentJ S.x
        · apply List.mem_append.mpr
          left
          have hEq : edgeTargetLists F S σ.1 c i j = σ.1.2.1 i j := by
            simp only [edgeTargetLists, ite_eq_left hj]
          rw [hEq]
          exact hσ.2 i _ (hOldActive i j)
        · rw [hAlabel i j hj]
          cases hc : (c i).2 with
          | inl k =>
              apply List.mem_append.mpr
              left
              have hNew : edgeNewLabel (c i) = ((σ.1.2.2 i).get k).1 := by
                simp only [edgeNewLabel, hc]
              rw [hNew]
              exact hσ.2 i _ (hOldMemory i _
                (List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩))
          | inr p =>
              apply List.mem_append.mpr
              right
              have hNew : edgeNewLabel (c i) = (p : ℕ) := by
                simp only [edgeNewLabel, hc]
              rw [hNew]
              exact hBirth i p hc
      · exact List.mem_append.mpr (Or.inl (hσ.2 i p (hRlive i p hR)))
    · exact List.mem_append.mpr (Or.inl (hσ.2 i p (hOlive i p hO)))

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
