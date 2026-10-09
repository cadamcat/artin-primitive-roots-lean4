import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedStep

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- The logged state after the ghost of visit `j` determined by `H`. -/
def IsLifeStateAfter {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x + 1))
    (τ : LogPoint S.x K) : Prop :=
  (τ.1.1, τ.1.2.1) = γ j ∧
    (∀ i, ((τ.1.2.2 i).map Prod.fst).Nodup) ∧
    (∀ i (q : Particle), q ∈ τ.1.2.2 i ↔
      ∃ hp : q.1 ∈ primeBand S.x (F.a i),
        pdLifePending S γ q.1 (H i ⟨q.1, hp⟩) true j ∧
          q.2 = (lifeLine S γ q.1 (H i ⟨q.1, hp⟩).1).val) ∧
    (τ.2.map Prod.snd).Nodup ∧
    ∀ p, p ∈ τ.2.map Prod.snd ↔
      (lifeBornBefore F S γ H p j ∨ ∃ i, lifeBornAt F S γ H i p j)

theorem mem_removeIndices_iff (l : List Particle) (D : Finset (Fin l.length))
    (q : Particle) : q ∈ removeIndices l D ↔ ∃ r : Fin l.length, r ∉ D ∧ l.get r = q := by
  unfold removeIndices
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨r, -, hr⟩
    by_cases hD : r ∈ D
    · simp [hD] at hr
    · exact ⟨r, hD, by simpa [hD] using hr⟩
  · rintro ⟨r, hD, hr⟩
    exact ⟨r, List.mem_finRange r, by simpa [hD] using hr⟩

/-- Facts on an active lifespan used below. -/
theorem life_active_facts {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (hA : (pdLifeActive S γ p).Nonempty) :
    (∀ j, IsActiveAt γ p j → (pdLifeActive S γ p).min' hA ≤ j ∧
        j ≤ (pdLifeActive S γ p).max' hA) ∧
      (∀ a, e.1.1 = some a → a < (pdLifeActive S γ p).min' hA ∧
        projLine p (γ a).1 = projLine p (γ ((pdLifeActive S γ p).min' hA)).1) ∧
      (∀ c, e.1.2 = some c → (pdLifeActive S γ p).max' hA < c) ∧
      (∀ j, IsActiveAt γ p j →
        projLine p (γ j).1 = projLine p (γ ((pdLifeActive S γ p).min' hA)).1) := by
  have hv : pdLifeEndpointValid S γ p e.1 := (Finset.mem_filter.mp e.2).2
  simp only [pdLifeEndpointValid, hA, ↓reduceDIte] at hv
  have hmemA : ∀ j, IsActiveAt γ p j → j ∈ pdLifeActive S γ p := by
    intro j hj
    simp [pdLifeActive, hj]
  refine ⟨fun j hj => ⟨Finset.min'_le _ _ (hmemA j hj), Finset.le_max' _ _ (hmemA j hj)⟩,
    ?_, ?_, fun j hj => hv.1 j (hmemA j hj)⟩
  · intro a ha
    have h2 := hv.2.1
    rw [ha] at h2
    exact h2
  · intro c hc
    have h3 := hv.2.2
    rw [hc] at h3
    exact h3.1

theorem life_inactive_facts {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (hA : ¬ (pdLifeActive S γ p).Nonempty) :
    e.1 = (none, none) ∨ ∃ a c, e.1 = (some a, some c) ∧ a < c ∧
      projLine p (γ c).1 = projLine p (γ a).1 := by
  have hv : pdLifeEndpointValid S γ p e.1 := (Finset.mem_filter.mp e.2).2
  simp only [pdLifeEndpointValid, hA, ↓reduceDIte] at hv
  rcases e with ⟨⟨_ | a, _ | c⟩, he⟩
  · exact Or.inl rfl
  · simp at hv
  · simp at hv
  · exact Or.inr ⟨a, c, rfl, hv⟩

theorem not_active_of_lt_min {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (hA : (pdLifeActive S γ p).Nonempty) (j : Fin (pathLength S.x + 1))
    (hj : j < (pdLifeActive S γ p).min' hA) : ¬ IsActiveAt γ p j := by
  intro hact
  have : j ∈ pdLifeActive S γ p := by simp [pdLifeActive, hact]
  exact absurd (Finset.min'_le _ _ this) (not_le.mpr hj)

/-- Pending after the ghost: pending before and not deleted, or born at the ghost. -/
theorem pending_true_iff {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (j : Fin (pathLength S.x + 1)) :
    pdLifePending S γ p e true j ↔
      (pdLifePending S γ p e false j ∧ e.1.2 ≠ some j) ∨ e.1.1 = some j := by
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · obtain ⟨hAJ, hB, hC, -⟩ := life_active_facts S γ p e hA
    have hαω := Finset.min'_le_max' _ hA
    simp only [pdLifePending, hA, ↓reduceDIte]
    rcases e with ⟨⟨_ | a, _ | c⟩, he⟩
    · by_cases hj : IsActiveAt γ p j
      · simp [hj]
      · simp only [hj, not_false_eq_true, true_and]
        split_ifs <;> simp
    · have hc := hC c rfl
      by_cases hj : IsActiveAt γ p j
      · simp [hj]
      · simp only [hj, not_false_eq_true, true_and, ↓reduceIte, ne_eq, Option.some.injEq,
          reduceCtorEq, or_false]
        split_ifs with h1 h2 <;> simp only [Fin.lt_def, Fin.le_def,
          Fin.ext_iff, not_lt, Bool.false_eq_true, ↓reduceIte, true_and, false_and, true_iff, false_iff, and_true,
          and_false, or_false, false_or, iff_true, iff_false, not_false_eq_true] at * <;> (first | omega | simp)
    · have ha := (hB a rfl).1
      by_cases hj : IsActiveAt γ p j
      · have := (hAJ j hj).1
        simp only [hj, not_true_eq_false, false_and, ne_eq, reduceCtorEq, not_false_eq_true,
          and_true, false_or, Option.some.injEq, false_iff]
        intro h; subst h; exact absurd ha (not_lt.mpr this)
      · simp only [hj, not_false_eq_true, true_and, ↓reduceIte, ne_eq, Option.some.injEq,
          reduceCtorEq]
        split_ifs with h1 h2 <;> simp only [Fin.lt_def, Fin.le_def,
          Fin.ext_iff, not_lt, Bool.false_eq_true, ↓reduceIte, true_and, false_and, true_iff, false_iff, and_true,
          and_false, or_false, false_or, iff_true, iff_false, not_false_eq_true] at * <;> (first | omega | simp)
    · have ha := (hB a rfl).1
      have hc := hC c rfl
      by_cases hj : IsActiveAt γ p j
      · have := hAJ j hj
        simp only [hj, not_true_eq_false, false_and, ne_eq, Option.some.injEq,
          false_or, false_iff]
        intro h; subst h; exact absurd ha (not_lt.mpr this.1)
      · simp only [hj, not_false_eq_true, true_and, ↓reduceIte, ne_eq, Option.some.injEq]
        split_ifs with h1 h2 <;> simp only [Fin.lt_def, Fin.le_def,
          Fin.ext_iff, not_lt, Bool.false_eq_true, ↓reduceIte, true_and, false_and, true_iff, false_iff, and_true,
          and_false, or_false, false_or, iff_true, iff_false, not_false_eq_true] at * <;> (first | omega | simp)
  · simp only [pdLifePending, hA, ↓reduceDIte]
    rcases life_inactive_facts S γ p e hA with h | ⟨a, c, h, hac, -⟩
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, ne_eq, Option.some.injEq]
      simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at *
      omega

theorem not_pending_false_of_born {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (j : Fin (pathLength S.x + 1)) (hb : e.1.1 = some j) :
    ¬ pdLifePending S γ p e false j := by
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · have ha := ((life_active_facts S γ p e hA).2.1 j hb).1
    simp only [pdLifePending, hA, ↓reduceDIte, ha, ↓reduceIte, hb]
    simp
  · simp only [pdLifePending, hA, ↓reduceDIte]
    rcases life_inactive_facts S γ p e hA with h | ⟨a, c, h, hac, -⟩
    · simp [h]
    · rw [h] at hb ⊢
      simp only [Option.some.injEq] at hb
      subst hb
      simp

theorem lifeLine_of_born {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (j : Fin (pathLength S.x + 1)) (hb : e.1.1 = some j) :
    lifeLine S γ p e.1 = projLine p (γ j).1 := by
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · have h := (life_active_facts S γ p e hA).2.1 j hb
    simp only [lifeLine, hA, ↓reduceDIte]
    exact h.2.symm
  · simp only [lifeLine, hA, ↓reduceDIte, hb]

theorem born_not_bornBefore {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (i : Fin K) (p : ℕ) (j : Fin (pathLength S.x + 1)) (hb : lifeBornAt F S γ H i p j) :
    ¬ lifeBornBefore F S γ H p j := by
  obtain ⟨hp, hb⟩ := hb
  rintro (⟨j', hj', hact⟩ | ⟨i', a, ha, hp', hb'⟩)
  · have hA : (pdLifeActive S γ p).Nonempty := ⟨j', by simp [pdLifeActive, hact]⟩
    have h1 := ((life_active_facts S γ p (H i ⟨p, hp⟩) hA).2.1 j hb).1
    have h2 := ((life_active_facts S γ p (H i ⟨p, hp⟩) hA).1 j' hact).1
    exact absurd (lt_of_lt_of_le h1 (le_trans h2 hj')) (lt_irrefl _)
  · by_cases hii : i' = i
    · subst hii
      rw [hb] at hb'
      cases hb'
      exact lt_irrefl _ ha
    · exact Finset.disjoint_left.mp (hBands i' i hii) hp' hp

theorem removeIndices_sublist' (l : List Particle)
    (D : Finset (Fin l.length)) : List.Sublist (removeIndices l D) l := by
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

theorem ghost_log_snd {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ) (σ : LogPoint S.x K)
    (g : GhostTraceChoice F S σ) :
    (ghostTraceOutput F S j σ g).2.map Prod.snd =
      σ.2.map Prod.snd ++ (List.finRange K).flatMap (fun i => (g.2 i).1.toList) := by
  unfold ghostTraceOutput subsetGhostPoint
  simp only [List.map_append, List.map_flatMap]
  congr 1
  apply congrArg (fun f => (List.finRange K).flatMap f)
  funext i
  rw [List.map_map]
  exact List.zipIdx_map_fst 0 _

/-- The guided ghost leads to the after-ghost life state. -/
theorem guided_ghost_output {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (H : PDLifeAssignment F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (j : Fin (pathLength S.x + 1)) (σ : LogPoint S.x K)
    (hσ : IsLifeState F S γ H j σ) :
    IsLifeStateAfter F S γ H j
      (ghostTraceOutput F S j.val σ (guidedGhostChoice F S γ H j σ)) := by
  obtain ⟨hpos, hnd, hmem, hlnd, hlmem⟩ := hσ
  have hz : σ.1.1 = (γ j).1 := congrArg Prod.fst hpos
  have hT (i : Fin K) (p : ℕ) :
      p ∈ ((guidedGhostChoice F S γ H j σ).2 i).1 ↔ lifeBornAt F S γ H i p j := by
    show p ∈ (primeBand S.x (F.a i)).filter _ ↔ _
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  have hmemOut (i : Fin K) :
      (ghostTraceOutput F S j.val σ (guidedGhostChoice F S γ H j σ)).1.2.2 i =
        removeIndices (σ.1.2.2 i) ((guidedGhostChoice F S γ H j σ).1 i) ++
          (((guidedGhostChoice F S γ H j σ).2 i).1.toList.map fun p => anchorAt p σ.1.1) :=
    rfl
  refine ⟨hpos, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hmemOut, List.map_append, List.map_map]
    have hfst : (Prod.fst ∘ fun p => anchorAt p σ.1.1) = id := by
      funext p; rfl
    rw [hfst, List.map_id]
    refine List.Nodup.append (((removeIndices_sublist' _ _).map Prod.fst).nodup (hnd i))
      (Finset.nodup_toList _) ?_
    intro a ha hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    obtain ⟨hp, hpend, -⟩ := (hmem i q).mp ((removeIndices_sublist' _ _).subset hq)
    obtain ⟨hp', hb'⟩ := (hT i q.1).mp (Finset.mem_toList.mp hb)
    exact not_pending_false_of_born S γ _ _ j hb' hpend
  · intro i q
    rw [hmemOut, List.mem_append, mem_removeIndices_iff, List.mem_map]
    constructor
    · rintro (⟨r, hr, rfl⟩ | ⟨p, hp, rfl⟩)
      · obtain ⟨hp, hpend, hanc⟩ := (hmem i _).mp (List.get_mem _ r)
        refine ⟨hp, (pending_true_iff S γ _ _ j).mpr (Or.inl ⟨hpend, fun hd => hr ?_⟩), hanc⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hp, hd⟩⟩
      · obtain ⟨hp', hb⟩ := (hT i p).mp (Finset.mem_toList.mp hp)
        refine ⟨hp', (pending_true_iff S γ _ _ j).mpr (Or.inr hb), ?_⟩
        show (projLine p σ.1.1).val = (lifeLine S γ p (H i ⟨p, hp'⟩).1).val
        rw [lifeLine_of_born S γ _ _ j hb, hz]
    · rintro ⟨hp, hpend, hanc⟩
      rcases (pending_true_iff S γ _ _ j).mp hpend with ⟨hpf, hnd'⟩ | hb
      · left
        obtain ⟨r, hr⟩ := List.mem_iff_get.mp ((hmem i q).mpr ⟨hp, hpf, hanc⟩)
        refine ⟨r, ?_, hr⟩
        intro hrD
        have hrD' : lifeDeletedAt F S γ H i ((σ.1.2.2 i).get r).1 j :=
          (Finset.mem_filter.mp hrD).2
        rw [hr] at hrD'
        obtain ⟨hp2, hd⟩ := hrD'
        exact hnd' hd
      · right
        refine ⟨q.1, Finset.mem_toList.mpr ((hT i q.1).mpr ⟨hp, hb⟩), ?_⟩
        refine Prod.ext ?_ ?_
        · rfl
        show (projLine q.1 σ.1.1).val = q.2
        rw [hanc, lifeLine_of_born S γ _ _ j hb, hz]
  · rw [ghost_log_snd]
    refine List.Nodup.append hlnd ?_ ?_
    · rw [List.nodup_flatMap]
      refine ⟨fun i _ => Finset.nodup_toList _, ?_⟩
      refine (List.nodup_finRange K).imp ?_
      intro i i' hii a ha ha'
      obtain ⟨hp, -⟩ := (hT i a).mp (Finset.mem_toList.mp ha)
      obtain ⟨hp', -⟩ := (hT i' a).mp (Finset.mem_toList.mp ha')
      exact Finset.disjoint_left.mp (hBands i i' hii) hp hp'
    · intro a ha hb
      obtain ⟨i, -, hai⟩ := List.mem_flatMap.mp hb
      exact born_not_bornBefore F S γ H hBands i a j ((hT i a).mp (Finset.mem_toList.mp hai))
        ((hlmem a).mp ha)
  · intro a
    rw [ghost_log_snd, List.mem_append, hlmem, List.mem_flatMap]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨i, -, hai⟩
      exact ⟨i, (hT i a).mp (Finset.mem_toList.mp hai)⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, List.mem_finRange i, Finset.mem_toList.mpr ((hT i a).mpr hi)⟩

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
