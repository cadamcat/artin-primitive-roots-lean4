import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedDefs

set_option autoImplicit false

/-! R2 of the `pd-birth-opus` route: the geometric edge factors multiply to the signed path
coefficient, the archimedean indicator, and the inverse active normalization. -/

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

private lemma omissionProduct_permuteLists' {x : ℝ} {K : ℕ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K)
    (omitted : Fin K → Fin (slotCount x)) :
    omissionProduct (permuteLists σ p) omitted =
      omissionProduct p (fun i => σ i (omitted i)) := by
  classical
  unfold omissionProduct
  apply Finset.prod_congr rfl
  intro i hi
  change (∏ j : Fin (slotCount x),
      if j ≠ omitted i then p i (σ i j) else 1) =
    ∏ j : Fin (slotCount x), if j ≠ σ i (omitted i) then p i j else 1
  apply Fintype.prod_equiv (σ i)
  intro j
  by_cases h : j = omitted i
  · subst j
    simp
  · have hmap : σ i j ≠ σ i (omitted i) := by
      intro heq
      exact h ((σ i).injective heq)
    simp [h, hmap]

private lemma goodnessTrialValue_permute' {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K)
    (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K) (fresh : Fin K → ℕ) (n : ℕ) :
    IsGoodnessTrialValue a (permuteLists σ p) d₀ I iStar fresh n ↔
      IsGoodnessTrialValue a p d₀ I iStar fresh n := by
  constructor
  · rintro ⟨omitted, z, hn, hlo, hhi, hz⟩
    let omitted' : Fin K → Fin (slotCount x) := fun i => σ i (omitted i)
    refine ⟨omitted', z, ?_, ?_, ?_, hz⟩
    · simpa [omitted', omissionProduct_permuteLists'] using hn
    · simpa [omitted', omissionProduct_permuteLists'] using hlo
    · simpa [omitted', omissionProduct_permuteLists'] using hhi
  · rintro ⟨omitted, z, hn, hlo, hhi, hz⟩
    let omitted' : Fin K → Fin (slotCount x) := fun i => (σ i).symm (omitted i)
    refine ⟨omitted', z, ?_, ?_, ?_, hz⟩
    · simpa [omitted', omissionProduct_permuteLists'] using hn
    · simpa [omitted', omissionProduct_permuteLists'] using hlo
    · simpa [omitted', omissionProduct_permuteLists'] using hhi

private lemma goodTestOne_permute' {x Y d₀ : ℝ} {K : ℕ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K) (r : ℝ) :
    goodTestOne x Y d₀ (permuteLists σ p) r ↔ goodTestOne x Y d₀ p r := by
  constructor
  · intro h omitted hlo hhi l hl₀ hl₁
    let omitted' : Fin K → Fin (slotCount x) := fun i => (σ i).symm (omitted i)
    have hprod : omissionProduct (permuteLists σ p) omitted' = omissionProduct p omitted := by
      simpa [omitted', omissionProduct_permuteLists']
    have hlo' : d₀ ≤ (omissionProduct (permuteLists σ p) omitted' : ℝ) := by
      rw [hprod]
      exact hlo
    have hhi' : (omissionProduct (permuteLists σ p) omitted' : ℝ) < 2 * d₀ := by
      rw [hprod]
      exact hhi
    have h := h omitted' hlo' hhi' l hl₀ hl₁
    simpa [hprod] using h
  · intro h omitted hlo hhi l hl₀ hl₁
    let omitted' : Fin K → Fin (slotCount x) := fun i => σ i (omitted i)
    have hprod : omissionProduct (permuteLists σ p) omitted = omissionProduct p omitted' := by
      simpa [omitted', omissionProduct_permuteLists']
    have hlo' : d₀ ≤ (omissionProduct p omitted' : ℝ) := by
      rw [← hprod]
      exact hlo
    have hhi' : (omissionProduct p omitted' : ℝ) < 2 * d₀ := by
      rw [← hprod]
      exact hhi
    have h := h omitted' hlo' hhi' l hl₀ hl₁
    simpa [hprod] using h

private lemma goodTestTwo_permute' {x d₀ : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K) (r : ℝ) :
    goodTestTwo x d₀ K a (permuteLists σ p) r ↔ goodTestTwo x d₀ K a p r := by
  constructor
  · intro h I hI
    simpa [goodTestTwo, goodnessTrialValue_permute'] using h I hI
  · intro h I hI
    simpa [goodTestTwo, goodnessTrialValue_permute'] using h I hI

theorem guided_envGood_permute {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (σ : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (s : EnvPoint S.x K) :
    envGood F S w (s.1, permuteLists σ s.2) ↔ envGood F S w s :=
  and_congr (goodTestOne_permute' σ s.2 _) (goodTestTwo_permute' F.a σ s.2 _)

theorem guided_validPrimeLists_permute {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K)
    (hp : ValidPrimeLists x K a p) : ValidPrimeLists x K a (permuteLists σ p) := by
  rcases hp with ⟨hband, hdistinct⟩
  constructor
  · intro i j
    simpa [permuteLists] using hband i (σ i j)
  · intro i j j' hj
    apply hdistinct i (σ i j) (σ i j')
    intro heq
    exact hj ((σ i).injective heq)

theorem guided_sharedProduct_eq {x : ℝ} {K : ℕ} (P Q : PrimeLists x K)
    (h : IsSlotTransition P Q) : sharedProduct Q = sharedProduct P := by
  unfold sharedProduct
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j.val < momentJ x
  · rw [if_pos hj, if_pos hj, h.1 i j hj]
  · rw [if_neg hj, if_neg hj]

theorem guided_slotTransition_symm {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (P Q : PrimeLists x K) (hP : ValidPrimeLists x K a P) (hQ : ValidPrimeLists x K a Q)
    (hBands : ∀ i i' : Fin K, i ≠ i' → Disjoint (primeBand x (a i)) (primeBand x (a i')))
    (h : IsSlotTransition P Q) : IsSlotTransition Q P := by
  refine ⟨fun i j hj => (h.1 i j hj).symm, ?_⟩
  intro i i' j
  by_cases hj : j.val < momentJ x
  · rw [h.1 i' j hj]
    by_cases hii : i = i'
    · subst hii
      apply hP.2 i
      intro heq
      have : (lastSlot x).val = j.val := congrArg Fin.val heq
      simp [lastSlot] at this
      omega
    · intro heq
      have h1 := (hP.1 i (lastSlot x)).2
      have h2 := (hP.1 i' j).2
      rw [heq] at h1
      exact Finset.disjoint_left.mp (hBands i i' hii) h1 h2
  · have hjl : j = lastSlot x := by
      apply Fin.ext
      have := j.isLt
      simp [lastSlot, slotCount] at this ⊢
      omega
    subst hjl
    exact fun heq => h.2 i' i (lastSlot x) heq.symm

theorem guided_pad_symm (d₀ D : ℕ) (z z' : ℤ × ℤ) :
    IsPadAdmissible d₀ D (det2 z' z) ↔ IsPadAdmissible d₀ D (det2 z z') := by
  have hdet : det2 z' z = -det2 z z' := by unfold det2; ring
  unfold IsPadAdmissible
  rw [hdet, dvd_neg]

/-- One edge: `c · edgeGeo = symKernel · [box and good tests at both ends]`, where
`c = ∏ V_i⁻¹` is the new-slot weight inside `slotKernel`. -/
theorem guided_edgeGeo_mul {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (j : Fin (pathLength S.x)) :
    (((∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ : ℝ)) : ℂ) * edgeGeo F S w γ j =
      symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ) *
        (if (envBox S w (γ j.castSucc).1 ∧ envGood F S w (γ j.castSucc)) ∧
            (envBox S w (γ j.succ).1 ∧ envGood F S w (γ j.succ)) then 1 else 0) := by
  set c : ℂ := (((∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ : ℝ)) : ℂ) with hc
  set ind : ℂ := (if (envBox S w (γ j.castSucc).1 ∧ envGood F S w (γ j.castSucc)) ∧
      (envBox S w (γ j.succ).1 ∧ envGood F S w (γ j.succ)) then 1 else 0) with hind
  have hValS := (hγ.1 j.castSucc).2
  have hValT := (hγ.1 j.succ).2
  have hgcdT := (hγ.1 j.succ).1
  let e : (Fin K → Equiv.Perm (Fin (slotCount S.x))) ≃
      (Fin K → Equiv.Perm (Fin (slotCount S.x))) :=
    Equiv.piCongrRight fun _ => Equiv.inv _
  unfold edgeGeo symKernel
  rw [mul_left_comm c, mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro π _
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv e _ _ ?_
  intro π'
  dsimp only
  have hP := guided_validPrimeLists_permute π (γ j.castSucc).2 hValS
  have hQ := guided_validPrimeLists_permute (e π') (γ j.succ).2 hValT
  have hGoodS := guided_envGood_permute F S w π (γ j.castSucc)
  have hGoodT := guided_envGood_permute F S w (e π') (γ j.succ)
  change c * (if ValidPrimeLists S.x K F.a (permuteLists π (γ j.castSucc).2) ∧
        ValidPrimeLists S.x K F.a (permuteLists (e π') (γ j.succ).2) ∧
        IsSlotTransition (permuteLists π (γ j.castSucc).2) (permuteLists (e π') (γ j.succ).2) ∧
        IsPadAdmissible S.d₀ (sharedProduct (permuteLists π (γ j.castSucc).2))
          (det2 (γ j.castSucc).1 (γ j.succ).1) ∧
        Int.gcd (γ j.succ).1.1 (γ j.succ).1.2 = 1 ∧ envBox S w (γ j.castSucc).1 ∧
        envBox S w (γ j.succ).1 ∧
        envGood F S w ((γ j.castSucc).1, permuteLists π (γ j.castSucc).2) ∧
        envGood F S w ((γ j.succ).1, permuteLists (e π') (γ j.succ).2) then
      edgeMultiplier F S (decide (j.val % 2 = 0)) true (permuteLists π (γ j.castSucc).2)
          (permuteLists (e π') (γ j.succ).2) (γ j.castSucc).1 (γ j.succ).1 -
        edgeMultiplier F S (decide (j.val % 2 = 0)) false (permuteLists π (γ j.castSucc).2)
          (permuteLists (e π') (γ j.succ).2) (γ j.castSucc).1 (γ j.succ).1
      else 0) = _
  generalize permuteLists π (γ j.castSucc).2 = P at hP hGoodS ⊢
  generalize permuteLists (e π') (γ j.succ).2 = Q at hQ hGoodT ⊢
  rw [hGoodS, hGoodT]
  simp only [hP, hQ, hgcdT, true_and]
  cases hfw : decide (j.val % 2 = 0)
  · -- adjoint edge
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold slotKernel edgeMultiplier
    simp only [Bool.false_eq_true, eq_self_iff_true, ↓reduceIte]
    by_cases hT : IsSlotTransition P Q
    · have hT' := guided_slotTransition_symm F.a P Q hP hQ hBands hT
      have hD := guided_sharedProduct_eq P Q hT
      rw [hD]
      by_cases hpad : IsPadAdmissible S.d₀ (sharedProduct P) (det2 (γ j.castSucc).1 (γ j.succ).1)
      · have hpad' : IsPadAdmissible S.d₀ (sharedProduct P)
            (det2 (γ j.succ).1 (γ j.castSucc).1) := (guided_pad_symm _ _ _ _).mpr hpad
        simp only [hT, hT', hpad, hpad', true_and, and_self, ↓reduceIte]
        unfold geometricMultiplier
        rw [star_mul', star_sub, Complex.star_def, Complex.conj_ofReal]
        rw [hind]
        split_ifs <;> first | ring1 | (exfalso; tauto)
      · have hpad' : ¬ IsPadAdmissible S.d₀ (sharedProduct P)
            (det2 (γ j.succ).1 (γ j.castSucc).1) := fun h => hpad ((guided_pad_symm _ _ _ _).mp h)
        simp only [hT, hT', hpad, hpad', true_and, false_and, and_false, ↓reduceIte,
          star_zero, mul_zero, zero_mul]
    · have hT' : ¬ IsSlotTransition Q P :=
        fun h => hT (guided_slotTransition_symm F.a Q P hQ hP hBands h)
      simp only [hT, hT', false_and, ↓reduceIte, star_zero, mul_zero, zero_mul]
  · -- forward edge
    simp only [↓reduceIte]
    unfold slotKernel edgeMultiplier
    simp only [eq_self_iff_true, ↓reduceIte]
    by_cases hT : IsSlotTransition P Q
    · by_cases hpad : IsPadAdmissible S.d₀ (sharedProduct P) (det2 (γ j.castSucc).1 (γ j.succ).1)
      · simp only [hT, hpad, true_and, ↓reduceIte]
        unfold geometricMultiplier
        rw [hind]
        split_ifs <;> first | ring1 | (exfalso; tauto)
      · simp only [hT, hpad, true_and, false_and, and_false, ↓reduceIte, mul_zero, zero_mul]
    · simp only [hT, false_and, ↓reduceIte, mul_zero, zero_mul]

/-- The archimedean edge indicators multiply to `pathArch` (every visit lies on an edge). -/
theorem guided_edge_arch_prod {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (γ : EnvPath S.x K) (hN : 0 < pathLength S.x) :
    (∏ j : Fin (pathLength S.x),
      (if (envBox S w (γ j.castSucc).1 ∧ envGood F S w (γ j.castSucc)) ∧
          (envBox S w (γ j.succ).1 ∧ envGood F S w (γ j.succ)) then (1 : ℂ) else 0)) =
      (pathArch F S w γ : ℂ) := by
  have hArch : (pathArch F S w γ : ℂ) =
      ∏ v, (if envBox S w (γ v).1 ∧ envGood F S w (γ v) then (1 : ℂ) else 0) := by
    unfold pathArch
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl (fun v _ => by split_ifs <;> simp)
  rw [hArch]
  by_cases hall : ∀ v : Fin (pathLength S.x + 1), envBox S w (γ v).1 ∧ envGood F S w (γ v)
  · rw [Finset.prod_eq_one (fun j _ => if_pos ⟨hall _, hall _⟩),
      Finset.prod_eq_one (fun v _ => if_pos (hall v))]
  · push_neg at hall
    obtain ⟨v, hv⟩ := hall
    have hv' : ¬ (envBox S w (γ v).1 ∧ envGood F S w (γ v)) := fun h => hv h.1 h.2
    have hR : (∏ v, (if envBox S w (γ v).1 ∧ envGood F S w (γ v) then (1 : ℂ) else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv')
    rw [hR]
    by_cases hvN : v.val < pathLength S.x
    · apply Finset.prod_eq_zero (Finset.mem_univ ⟨v.val, hvN⟩)
      have : (⟨v.val, hvN⟩ : Fin (pathLength S.x)).castSucc = v := Fin.ext rfl
      rw [this, if_neg (fun h => hv' h.1)]
    · have hvl : v.val = pathLength S.x := by have := v.isLt; omega
      apply Finset.prod_eq_zero (Finset.mem_univ ⟨pathLength S.x - 1, by omega⟩)
      have : (⟨pathLength S.x - 1, by omega⟩ : Fin (pathLength S.x)).succ = v := by
        apply Fin.ext
        simp
        omega
      rw [this, if_neg (fun h => hv' h.2)]

/-- R2: the geometric edge factors multiply to the path coefficient, the archimedean factor,
and the inverse active normalization. -/
theorem edgeGeo_prod {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (hMass : ∀ i, 0 < bandMass S.x (F.a i)) (hN : 0 < pathLength S.x) :
    ∏ j : Fin (pathLength S.x), edgeGeo F S w γ j =
      pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
        (((pdActiveNormalization F S)⁻¹ : ℝ) : ℂ) := by
  have hcR : (∏ i : Fin K, (bandMass S.x (F.a i))⁻¹) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => inv_ne_zero (ne_of_gt (hMass i)))
  have hc : (((∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast hcR
  have hphysR : physicalMeasure S.x K F.a ≠ 0 := by
    unfold physicalMeasure
    exact Finset.prod_ne_zero_iff.mpr
      (fun i _ => ne_of_gt (Real.rpow_pos_of_pos (hMass i) _))
  have hkey : (((∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ : ℝ)) : ℂ) ^ pathLength S.x *
      ∏ j : Fin (pathLength S.x), edgeGeo F S w γ j =
      (∏ j : Fin (pathLength S.x),
        symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ)) *
        (pathArch F S w γ : ℂ) := by
    rw [← guided_edge_arch_prod F S w γ hN, ← Finset.prod_mul_distrib]
    rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => guided_edgeGeo_mul F S w γ hγ hBands j)
  have hpow : (((∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ : ℝ)) : ℂ) ^ pathLength S.x ≠ 0 :=
    pow_ne_zero _ hc
  have hgeo : ∏ j : Fin (pathLength S.x), edgeGeo F S w γ j =
      (∏ j : Fin (pathLength S.x),
        symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ)) *
        (pathArch F S w γ : ℂ) /
        (((∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ : ℝ)) : ℂ) ^ pathLength S.x := by
    rw [eq_div_iff hpow, mul_comm]
    exact hkey
  rw [hgeo]
  unfold pathCoefficient pdActiveNormalization
  have hphys : (physicalMeasure S.x K F.a : ℂ) ≠ 0 := by exact_mod_cast hphysR
  rw [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_pow, div_eq_iff hpow, mul_inv]
  calc _ = (∏ j : Fin (pathLength S.x),
        symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ)) *
          (pathArch F S w γ : ℂ) *
          ((physicalMeasure S.x K F.a : ℂ) * (physicalMeasure S.x K F.a : ℂ)⁻¹) *
          ((((∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ : ℝ)) : ℂ) ^ pathLength S.x *
            ((((∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ : ℝ)) : ℂ) ^ pathLength S.x)⁻¹) := by
        rw [mul_inv_cancel₀ hphys, mul_inv_cancel₀ hpow, mul_one, mul_one]
    _ = _ := by ring
