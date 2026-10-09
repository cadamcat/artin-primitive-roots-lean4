import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CleanCoreFinite

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD
open scoped BigOperators

noncomputable section

/-- The physical clean core ignores endpoints outside its finite admissible masks. -/
theorem clean_core_physical_endpoint_restriction {K : ℕ}
    (F : PDFix K) (hF : F.Valid) (S : PDScale) (hY : 0 < S.Y)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ)
    (I : Finset (MemPoint S.x K)) (f : MemPoint S.x K → ℂ)
    (hf : ∀ t, t ∉ I → f t = 0) (s : MemPoint S.x K) :
    let P := fun t : MemPoint S.x K =>
      MemValid F S t ∧ ValidPrimeLists S.x K F.a t.2.1 ∧
      S.Y ≤ (lastProduct t.2.1 : ℝ) ∧
      (S.d₀ : ℝ) ≤ (sharedProduct t.2.1 : ℝ) ∧
      (sharedProduct t.2.1 : ℝ) < 2*(S.d₀ : ℝ) ∧
      envBox S w t.1 ∧ envGood F S w (t.1, t.2.1)
    let core := fun g : MemPoint S.x K → ℂ =>
      fun t : MemPoint S.x K =>
        plainOp (logEdgePiece F S ρ w j true ∅ ∅) g t-
          plainOp (logEdgePiece F S ρ w j false ∅ ∅) g t
    memMeasure F S s*‖core f s‖^2 =
      if P s then
        memMeasure F S s*‖core (fun t => if P t then f t else 0) s‖^2
      else 0 := by
  classical
  let P := fun t : MemPoint S.x K =>
    MemValid F S t ∧ ValidPrimeLists S.x K F.a t.2.1 ∧
    S.Y ≤ (lastProduct t.2.1 : ℝ) ∧
    (S.d₀ : ℝ) ≤ (sharedProduct t.2.1 : ℝ) ∧
    (sharedProduct t.2.1 : ℝ) < 2*(S.d₀ : ℝ) ∧
    envBox S w t.1 ∧ envGood F S w (t.1, t.2.1)
  let core := fun (g : MemPoint S.x K → ℂ) (t : MemPoint S.x K) =>
    plainOp (logEdgePiece F S ρ w j true ∅ ∅) g t-
      plainOp (logEdgePiece F S ρ w j false ∅ ∅) g t
  change memMeasure F S s*‖core f s‖^2 =
    if P s then memMeasure F S s*‖core (fun t => if P t then f t else 0) s‖^2 else 0
  by_cases hsvalid : MemValid F S s
  · let μ := fun t : MemPoint S.x K =>
      ∏ i : Fin K, memoryNu S.x K F.a F.q_d i (t.2.1 i (lastSlot S.x))
    let adm := fun t : MemPoint S.x K =>
      s.2.2 = t.2.2 ∧ ValidPrimeLists S.x K F.a s.2.1 ∧
      ValidPrimeLists S.x K F.a t.2.1 ∧ IsSlotTransition s.2.1 t.2.1 ∧
      IsPadAdmissible S.d₀ (sharedProduct s.2.1) (det2 s.1 t.1) ∧
      Int.gcd t.1.1 t.1.2 = 1 ∧ envBox S w s.1 ∧ envBox S w t.1 ∧
      envGood F S w (s.1, s.2.1) ∧ envGood F S w (t.1, t.2.1)
    let k := fun t : MemPoint S.x K =>
      if decide (j % 2 = 0) then
        geometricMultiplier F S (sharedProduct s.2.1) (lastProduct t.2.1)
          (lastProduct s.2.1) (det2 s.1 t.1/(sharedProduct s.2.1 : ℤ))
      else star (geometricMultiplier F S (sharedProduct s.2.1) (lastProduct s.2.1)
        (lastProduct t.2.1) (det2 t.1 s.1/(sharedProduct s.2.1 : ℤ)))
    let damp := fun t : MemPoint S.x K =>
      (ρ^(∑ i : Fin K, hitCount (t.2.2 i) t.1) : ℂ)
    have hη (n : ℕ) (hn : ¬ S.Y ≤ (n : ℝ)) : F.eta ((n : ℝ)/S.Y) = 0 := by
      by_contra hne
      have hsupport := hF.2.2.2.2.1.2.1 (show (n : ℝ)/S.Y ∈ Function.support F.eta from hne)
      have hlow := (le_div_iff₀ hY).mp hsupport.1
      exact hn (by simpa only [one_mul] using hlow)
    have hgzero (D a b : ℕ) (z : ℤ)
        (hn : ¬ S.Y ≤ (a : ℝ) ∨ ¬ S.Y ≤ (b : ℝ)) :
        geometricMultiplier F S D a b z = 0 := by
      rcases hn with ha | hb
      · simp only [geometricMultiplier, rawMultiplier, comparisonMultiplier, hη a ha,
          Complex.ofReal_zero, mul_zero, zero_mul, sub_self]
      · simp only [geometricMultiplier, rawMultiplier, comparisonMultiplier, hη b hb,
          Complex.ofReal_zero, mul_zero, zero_mul, sub_self]
    have hkzero (t : MemPoint S.x K)
        (hn : ¬ S.Y ≤ (lastProduct s.2.1 : ℝ) ∨ ¬ S.Y ≤ (lastProduct t.2.1 : ℝ)) :
        k t = 0 := by
      dsimp only [k]
      split_ifs
      · exact hgzero _ _ _ _ hn.symm
      · rw [hgzero _ _ _ _ hn, star_zero]
    have hend (t : MemPoint S.x K) (ha : adm t) (hk : k t ≠ 0) : P s ∧ P t := by
      obtain ⟨hmem, hsp, htp, hslot, hpad, htprim, hsbox, htbox, hsgood, htgood⟩ := ha
      have hlasts : S.Y ≤ (lastProduct s.2.1 : ℝ) := by
        by_contra hn
        exact hk (hkzero t (Or.inl hn))
      have hlastt : S.Y ≤ (lastProduct t.2.1 : ℝ) := by
        by_contra hn
        exact hk (hkzero t (Or.inr hn))
      have htvalid : MemValid F S t := by
        refine ⟨htprim, fun i jj => (htp.1 i jj).2, ?_⟩
        rw [← hmem]
        exact hsvalid.2.2
      have hD : sharedProduct t.2.1 = sharedProduct s.2.1 := by
        unfold sharedProduct
        apply Finset.prod_congr rfl
        intro i hi
        apply Finset.prod_congr rfl
        intro jj hjj
        by_cases hj : jj.val < momentJ S.x
        · simp only [if_pos hj, hslot.1 i jj hj]
        · simp only [if_neg hj]
      refine ⟨⟨hsvalid, hsp, hlasts, hpad.1, hpad.2.1, hsbox, hsgood⟩,
        ⟨htvalid, htp, hlastt, ?_, ?_, htbox, htgood⟩⟩
      · rw [hD]; exact hpad.1
      · rw [hD]; exact hpad.2.1
    let fP := fun t : MemPoint S.x K => if P t then f t else 0
    have hfP : ∀ t, t ∉ I → fP t = 0 := by
      intro t ht
      simp only [fP, hf t ht, ite_self]
    have hformula (g : MemPoint S.x K → ℂ) (hg : ∀ t, t ∉ I → g t = 0) :
        core g s = damp s*(∑ t ∈ I, if adm t then k t*(μ t : ℂ)*damp t*g t else 0) :=
      clean_core_finite_formula F S ρ w j I g hg s
    have hpoint (t : MemPoint S.x K) :
        (if adm t then k t*(μ t : ℂ)*damp t*f t else 0) =
        if P s then (if adm t then k t*(μ t : ℂ)*damp t*fP t else 0) else 0 := by
      by_cases ha : adm t
      · by_cases hk : k t = 0
        · simp only [if_pos ha, hk, zero_mul, ite_self]
        · obtain ⟨hsP, htP⟩ := hend t ha hk
          simp only [if_pos ha, if_pos hsP, fP, if_pos htP]
      · simp only [if_neg ha, ite_self]
    have hrow : core f s = if P s then core fP s else 0 := by
      rw [hformula f hf, hformula fP hfP]
      by_cases hsP : P s
      · rw [if_pos hsP]
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        exact (hpoint t).trans (if_pos hsP)
      · rw [if_neg hsP]
        have hsum : (∑ t ∈ I, if adm t then k t*(μ t : ℂ)*damp t*f t else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          exact (hpoint t).trans (if_neg hsP)
        rw [hsum, mul_zero]
    rw [hrow]
    by_cases hsP : P s <;> simp only [fP, hsP, if_true, if_false, norm_zero, zero_pow
      (by decide : (2 : ℕ) ≠ 0), mul_zero]
  · have hmeasure : memMeasure F S s = 0 := by simp only [memMeasure, if_neg hsvalid]
    simp only [hmeasure, zero_mul, ite_self]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
