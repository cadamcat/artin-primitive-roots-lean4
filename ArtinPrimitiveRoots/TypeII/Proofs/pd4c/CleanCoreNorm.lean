import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CleanEndpoints

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD
open scoped BigOperators

noncomputable section

/-- The physical-mask bound controls the unsymmetrized clean core on all finite supports. -/
theorem clean_core_norm_of_physical_masks {K : ℕ}
    (F : PDFix K) (hF : F.Valid) (S : PDScale) (hY : 0 < S.Y)
    (ρ : ℝ) (w : ArchRoot) (j B : ℕ) (R : ℝ)
    (hm : ∀ s : MemPoint S.x K, 0 ≤ memMeasure F S s) :
    let P := fun t : MemPoint S.x K =>
      MemValid F S t ∧ ValidPrimeLists S.x K F.a t.2.1 ∧
      S.Y ≤ (lastProduct t.2.1 : ℝ) ∧
      (S.d₀ : ℝ) ≤ (sharedProduct t.2.1 : ℝ) ∧
      (sharedProduct t.2.1 : ℝ) < 2*(S.d₀ : ℝ) ∧
      envBox S w t.1 ∧ envGood F S w (t.1, t.2.1)
    let μ := fun t : MemPoint S.x K =>
      ∏ i : Fin K, memoryNu S.x K F.a F.q_d i (t.2.1 i (lastSlot S.x))
    let adm := fun s t : MemPoint S.x K =>
      s.2.2 = t.2.2 ∧ IsSlotTransition s.2.1 t.2.1 ∧
      IsPadAdmissible S.d₀ (sharedProduct s.2.1) (det2 s.1 t.1)
    let k := fun s t : MemPoint S.x K => if adm s t then
      edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1 t.2.1 s.1 t.1-
        edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1 t.2.1 s.1 t.1 else 0
    (∀ T : Finset (MemPoint S.x K), (∀ s ∈ T, P s) →
      ∀ I O : Finset (MemPoint S.x K), I ⊆ T → O ⊆ T →
      ∀ f : MemPoint S.x K → ℂ,
      (∑ s ∈ O, memMeasure F S s*‖(ρ^(∑ i : Fin K, hitCount (s.2.2 i) s.1) : ℂ)*
        (∑ t ∈ I, k s t*(μ t : ℂ)*
          (ρ^(∑ i : Fin K, hitCount (t.2.2 i) t.1) : ℂ)*f t)‖^2) ≤
        R^2*(∑ t ∈ I, memMeasure F S t*‖f t‖^2)) →
    MemOpNormLE F S B
      (fun f s => plainOp (logEdgePiece F S ρ w j true ∅ ∅) f s-
        plainOp (logEdgePiece F S ρ w j false ∅ ∅) f s) R := by
  classical
  intro P μ adm k hbound
  let core := fun (g : MemPoint S.x K → ℂ) (s : MemPoint S.x K) =>
    plainOp (logEdgePiece F S ρ w j true ∅ ∅) g s-
      plainOp (logEdgePiece F S ρ w j false ∅ ∅) g s
  let damp := fun s : MemPoint S.x K =>
    (ρ^(∑ i : Fin K, hitCount (s.2.2 i) s.1) : ℂ)
  intro I O f hf _hIsize _hOsize
  let I1 := I.filter P
  let O1 := O.filter P
  let fP := fun t : MemPoint S.x K => if P t then f t else 0
  have hfP : ∀ t, t ∉ I1 → fP t = 0 := by
    intro t ht
    by_cases hp : P t
    · have htI : t ∉ I := fun hi => ht (Finset.mem_filter.mpr ⟨hi, hp⟩)
      simp only [fP, if_pos hp, hf t htI]
    · simp only [fP, if_neg hp]
  have houtput : memNormSqOn F S O (core f) = memNormSqOn F S O1 (core fP) := by
    dsimp only [memNormSqOn, O1]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s hs
    exact clean_core_physical_endpoint_restriction F hF S hY ρ w j I f hf s
  have hrow (s : MemPoint S.x K) (hs : s ∈ O1) :
      core fP s = damp s*(∑ t ∈ I1, k s t*(μ t : ℂ)*damp t*fP t) := by
    have hsP := (Finset.mem_filter.mp hs).2
    let A := fun t : MemPoint S.x K =>
      s.2.2 = t.2.2 ∧ ValidPrimeLists S.x K F.a s.2.1 ∧
      ValidPrimeLists S.x K F.a t.2.1 ∧ IsSlotTransition s.2.1 t.2.1 ∧
      IsPadAdmissible S.d₀ (sharedProduct s.2.1) (det2 s.1 t.1) ∧
      Int.gcd t.1.1 t.1.2 = 1 ∧ envBox S w s.1 ∧ envBox S w t.1 ∧
      envGood F S w (s.1, s.2.1) ∧ envGood F S w (t.1, t.2.1)
    let k0 := fun t : MemPoint S.x K =>
      if decide (j % 2 = 0) then
        geometricMultiplier F S (sharedProduct s.2.1) (lastProduct t.2.1)
          (lastProduct s.2.1) (det2 s.1 t.1/(sharedProduct s.2.1 : ℤ))
      else star (geometricMultiplier F S (sharedProduct s.2.1) (lastProduct s.2.1)
        (lastProduct t.2.1) (det2 t.1 s.1/(sharedProduct s.2.1 : ℤ)))
    have hadm (t : MemPoint S.x K) (ht : t ∈ I1) : A t ↔ adm s t := by
      have htP := (Finset.mem_filter.mp ht).2
      constructor
      · intro ha
        exact ⟨ha.1, ha.2.2.2.1, ha.2.2.2.2.1⟩
      · intro ha
        exact ⟨ha.1, hsP.2.1, htP.2.1, ha.2.1, ha.2.2, htP.1.1,
          hsP.2.2.2.2.2.1, htP.2.2.2.2.2.1, hsP.2.2.2.2.2.2, htP.2.2.2.2.2.2⟩
    have hmult (t : MemPoint S.x K) :
        edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1 t.2.1 s.1 t.1-
          edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1 t.2.1 s.1 t.1 = k0 t := by
      dsimp only [edgeMultiplier, k0, geometricMultiplier]
      cases he : decide (j % 2 = 0) <;> simp only [he, Bool.false_eq_true, if_false,
        if_true, star_sub]
    have hformula := clean_core_finite_formula F S ρ w j I1 fP hfP s
    change core fP s = damp s*(∑ t ∈ I1, if A t then k0 t*(μ t : ℂ)*damp t*fP t else 0)
      at hformula
    rw [hformula]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    by_cases ha : adm s t
    · simp only [if_pos ((hadm t ht).mpr ha), k, if_pos ha, hmult t]
    · have hn : ¬ A t := fun h => ha ((hadm t ht).mp h)
      simp only [if_neg hn, k, if_neg ha, zero_mul]
  have hT : ∀ s ∈ I1 ∪ O1, P s := by
    intro s hs
    rcases Finset.mem_union.mp hs with hi | ho
    · exact (Finset.mem_filter.mp hi).2
    · exact (Finset.mem_filter.mp ho).2
  have hmask := hbound (I1 ∪ O1) hT I1 O1 (Finset.subset_union_left)
    (Finset.subset_union_right) fP
  have hnorm : memNormSqOn F S O1 (core fP) ≤ R^2*memNormSqOn F S I1 fP := by
    calc
      _ = ∑ s ∈ O1, memMeasure F S s*‖damp s*(∑ t ∈ I1,
          k s t*(μ t : ℂ)*damp t*fP t)‖^2 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hrow s hs]
      _ ≤ _ := hmask
  have hinput : memNormSqOn F S I1 fP ≤ memNormSqOn F S I f := by
    calc
      _ = memNormSqOn F S I1 f := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [fP, if_pos (Finset.mem_filter.mp ht).2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun t ht hnot => mul_nonneg (hm t) (sq_nonneg _))
  change memNormSqOn F S O (core f) ≤ R^2*memNormSqOn F S I f
  rw [houtput]
  exact hnorm.trans (mul_le_mul_of_nonneg_left hinput (sq_nonneg R))

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
