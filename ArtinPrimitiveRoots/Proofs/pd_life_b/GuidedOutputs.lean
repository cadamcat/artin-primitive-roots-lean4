import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedUnique

set_option autoImplicit false

/-! Structural description of ghost and edge outputs (any choices). -/

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

theorem ghost_mem_iff {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ) (σ : LogPoint S.x K)
    (g : GhostTraceChoice F S σ) (i : Fin K) (q : Particle) :
    q ∈ (ghostTraceOutput F S j σ g).1.2.2 i ↔
      (∃ r : Fin (σ.1.2.2 i).length, r ∉ g.1 i ∧ (σ.1.2.2 i).get r = q) ∨
        (q.1 ∈ (g.2 i).1 ∧ q = anchorAt q.1 σ.1.1) := by
  show q ∈ removeIndices (σ.1.2.2 i) (g.1 i) ++
    ((g.2 i).1.toList.map fun p => anchorAt p σ.1.1) ↔ _
  rw [List.mem_append, mem_removeIndices_iff, List.mem_map]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Finset.mem_toList.mp hp, rfl⟩
  · rintro ⟨hp, hq⟩
    exact ⟨q.1, Finset.mem_toList.mpr hp, hq.symm⟩

theorem ghost_log_iff {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ) (σ : LogPoint S.x K)
    (g : GhostTraceChoice F S σ) (p : ℕ) :
    p ∈ (ghostTraceOutput F S j σ g).2.map Prod.snd ↔
      p ∈ σ.2.map Prod.snd ∨ ∃ i, p ∈ (g.2 i).1 := by
  rw [ghost_log_snd, List.mem_append, List.mem_flatMap]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨i, -, h⟩; exact ⟨i, Finset.mem_toList.mp h⟩
  · rintro ⟨i, h⟩; exact ⟨i, List.mem_finRange i, Finset.mem_toList.mpr h⟩

theorem edge_mem_iff {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ) (z' : ℤ × ℤ)
    (τ : LogPoint S.x K) (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i) (i : Fin K) (q : Particle) :
    q ∈ (edgeTraceOutput F S j z' τ (π, c, π')).1.2.2 i ↔
      (∃ r : Fin (τ.1.2.2 i).length, (c i).2 ≠ Sum.inl r ∧ (τ.1.2.2 i).get r = q) ∨
        ((c i).1 = true ∧ q = anchorAt (permuteLists π τ.1.2.1 i (lastSlot S.x)) τ.1.1) := by
  show q ∈ edgeNewMemory F S (permuteLogPoint π τ).1 c i ↔ _
  unfold edgeNewMemory
  rw [List.mem_append, mem_removeIndices_iff]
  apply or_congr
  · constructor
    · rintro ⟨r, hr, hq⟩
      refine ⟨r, ?_, hq⟩
      intro hc
      apply hr
      rw [hc]
      exact Finset.mem_singleton_self r
    · rintro ⟨r, hr, hq⟩
      refine ⟨r, ?_, hq⟩
      cases hc : (c i).2 with
      | inl k =>
        intro hrk
        simp at hrk
        have hrk' : r = k := Finset.mem_singleton.mp hrk
        subst hrk'
        exact hr hc
      | inr _ => simp only [hc]; exact Finset.notMem_empty r
  · cases hb : (c i).1 <;> simp [permuteLogPoint, eq_comm]

theorem edge_list_iff {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ) (z' : ℤ × ℤ)
    (τ : LogPoint S.x K) (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i) (p : ℕ) :
    (∃ i jj, (edgeTraceOutput F S j z' τ (π, c, π')).1.2.1 i jj = p) ↔
      (∃ i, ∃ y : Fin (slotCount S.x), y.val < momentJ S.x ∧ permuteLists π τ.1.2.1 i y = p) ∨
        ∃ i, edgeNewLabel (c i) = p := by
  have hL : ∀ i jj, (edgeTraceOutput F S j z' τ (π, c, π')).1.2.1 i jj =
      if (π' i jj).val < momentJ S.x then permuteLists π τ.1.2.1 i (π' i jj)
      else edgeNewLabel (c i) := fun _ _ => rfl
  constructor
  · rintro ⟨i, jj, h⟩
    rw [hL] at h
    split_ifs at h with hy
    · exact Or.inl ⟨i, _, hy, h⟩
    · exact Or.inr ⟨i, h⟩
  · rintro (⟨i, y, hy, h⟩ | ⟨i, h⟩)
    · refine ⟨i, (π' i).symm y, ?_⟩
      rw [hL]; simp [hy, h]
    · refine ⟨i, (π' i).symm (lastSlot S.x), ?_⟩
      rw [hL]; simp [lastSlot, h]

theorem edge_log_iff {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ) (z' : ℤ × ℤ)
    (τ : LogPoint S.x K) (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i) (p : ℕ) :
    p ∈ (edgeTraceOutput F S j z' τ (π, c, π')).2.map Prod.snd ↔
      p ∈ τ.2.map Prod.snd ∨ ∃ i, ∃ q : primeBand S.x (F.a i), (c i).2 = Sum.inr q ∧ q.1 = p := by
  show p ∈ (τ.2 ++ edgeBirths F S j (permuteLogPoint π τ).1 c).map Prod.snd ↔ _
  rw [List.map_append, List.mem_append]
  apply or_congr Iff.rfl
  unfold edgeBirths
  rw [List.map_flatMap, List.mem_flatMap]
  constructor
  · rintro ⟨i, -, h⟩
    refine ⟨i, ?_⟩
    revert h
    cases hc : (c i).2 with
    | inl k => intro h; simp at h
    | inr q => intro h; simp at h; exact ⟨q, rfl, h.symm⟩
  · rintro ⟨i, q, hc, rfl⟩
    refine ⟨i, List.mem_finRange i, ?_⟩
    simp [hc]

/-- A fresh fill with an already logged prime makes the output log repeat. -/
theorem edge_fresh_not_logged {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ) (z' : ℤ × ℤ)
    (τ : LogPoint S.x K) (π π' : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (τ.1.2.2 i) i)
    (hnd : ((edgeTraceOutput F S j z' τ (π, c, π')).2.map Prod.snd).Nodup)
    (i : Fin K) (q : primeBand S.x (F.a i)) (hc : (c i).2 = Sum.inr q) :
    q.1 ∉ τ.2.map Prod.snd := by
  intro hq
  have hnd' : (τ.2.map Prod.snd ++
      (edgeBirths F S j (permuteLogPoint π τ).1 c).map Prod.snd).Nodup := by
    rw [← List.map_append]; exact hnd
  apply List.disjoint_of_nodup_append hnd' hq
  unfold edgeBirths
  rw [List.map_flatMap, List.mem_flatMap]
  exact ⟨i, List.mem_finRange i, by simp [hc]⟩

/-- A ghost birth of an already logged prime makes the output log repeat. -/
theorem ghost_born_not_logged {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ)
    (σ : LogPoint S.x K) (g : GhostTraceChoice F S σ)
    (hnd : ((ghostTraceOutput F S j σ g).2.map Prod.snd).Nodup)
    (i : Fin K) (p : ℕ) (hp : p ∈ (g.2 i).1) : p ∉ σ.2.map Prod.snd := by
  intro hq
  rw [ghost_log_snd] at hnd
  apply List.disjoint_of_nodup_append hnd hq
  exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, Finset.mem_toList.mpr hp⟩

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
