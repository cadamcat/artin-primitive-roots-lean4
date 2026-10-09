import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.RawActualEndpoint
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Damping

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- The indices still free after fixing one distinguished promoted particle. -/
abbrev RawPromotionIndices {K : ℕ} (I : Finset (Fin K)) (iStar : Fin K)
    (m : Fin K → List Particle) :=
  (i : I.erase iStar) → Fin (m i.1).length

/-- Numeric labels carried by the remaining promoted indices. -/
def rawPromotionLabels {K : ℕ} (I : Finset (Fin K)) (iStar : Fin K)
    (m : Fin K → List Particle) (κ : RawPromotionIndices I iStar m) : Fin K → ℕ :=
  fun i => if hi : i ∈ I.erase iStar then ((m i).get (κ ⟨i, hi⟩)).1 else 1

/-- Good fresh draws admit one determinant and one omission fiber; outgoing damping
absorbs the remaining indexed multiplicities before source symmetrization. -/
theorem raw_good_anchor_grouped_damping_average {K : ℕ} (S : PDScale) (a : Fin K → ℝ)
    (p : PrimeLists S.x K) (hp : ValidPrimeLists S.x K a p)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand S.x (a i)) (primeBand S.x (a j)))
    (I : Finset (Fin K)) (iStar : Fin K) (fresh : Fin K → ℕ)
    (hfresh : IsFreshChoice S.x a I fresh) (w : ArchRoot) (e : Particle)
    (he : e.1.Prime) (hband : e.1 ∈ primeBand S.x (a iStar))
    (hban : ∀ i j, e.1 ≠ p i j) (z : ℤ × ℤ) (hz : Int.gcd z.1 z.2 = 1)
    (hU : 0 < S.U) (hw : w.InRegion S) (hbox : envBox S w z)
    (hfin : {z' : ℤ × ℤ | envBox S w z'}.Finite)
    (hsep : ∀ n₁ n₂, IsGoodnessTrialValue a p (S.d₀ : ℝ) I iStar fresh n₁ →
      IsGoodnessTrialValue a p (S.d₀ : ℝ) I iStar fresh n₂ → n₁ ≠ n₂ →
      100 * Real.exp (-Real.rpow (Real.log S.x) (a iStar)) <
        circleDistance (((n₁ : ℝ) - n₂) * transportedRatio w z))
    (m : Fin K → List Particle) (T : Finset (ℤ × ℤ))
    (ρ C : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (W : (Fin K → Equiv.Perm (Fin (slotCount S.x))) →
      RawPromotionIndices I iStar m → (ℤ × ℤ) → ℝ)
    (hW : ∀ σ κ z', W σ κ z' ≤ C *
      ∏ i : I.erase iStar,
        if particleHits ((m i.1).get (κ i)) z'
        then ρ ^ (hitCount (m i.1) z' - 1) else 0)
    (hsupport : ∀ σ κ z', W σ κ z' ≠ 0 →
      RawAnchorEndpoint S a p I iStar fresh w e z
        (fun i => σ i (lastSlot S.x)) (rawPromotionLabels I iStar m κ) z') :
    (permCount S.x K : ℝ)⁻¹ *
      ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        ∑ z' ∈ T, ∑ κ : RawPromotionIndices I iStar m, W σ κ z' ≤
      (34 * C * (1 / (1 - ρ) ^ 2) ^ K) / (slotCount S.x : ℝ) ^ K := by
  let A : ℝ := 1 / (1 - ρ) ^ 2
  have hden : 0 < 1 - ρ := by linarith
  have hden1 : 1 - ρ ≤ 1 := by linarith
  have hsq : (1 - ρ) ^ 2 ≤ 1 := by
    nlinarith [mul_self_le_mul_self hden.le hden1]
  have hA : 1 ≤ A := (one_le_div (sq_pos_of_pos hden)).mpr hsq
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hcount : (I.erase iStar).card ≤ K := by
    simpa using Finset.card_le_univ (I.erase iStar)
  have hpow : A ^ (I.erase iStar).card ≤ A ^ K := pow_le_pow_right₀ hA hcount
  let H (z' : ℤ × ℤ) (i : I.erase iStar) (k : Fin (m i.1).length) : ℝ :=
    if particleHits ((m i.1).get k) z' then ρ ^ (hitCount (m i.1) z' - 1) else 0
  have hH : ∀ z' i k, 0 ≤ H z' i k := by
    intro z' i k
    dsimp only [H]
    split_ifs <;> positivity
  have hindex (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) (z' : ℤ × ℤ) :
      (∑ κ : RawPromotionIndices I iStar m, W σ κ z') ≤ C * A ^ K := by
    calc
      _ ≤ ∑ κ : RawPromotionIndices I iStar m,
          C * ∏ i : I.erase iStar, H z' i (κ i) :=
        Finset.sum_le_sum (fun κ hκ => hW σ κ z')
      _ = C * ∏ i : I.erase iStar, ∑ k : Fin (m i.1).length, H z' i k := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Fintype.piFinset_univ]
        simpa using (Finset.prod_univ_sum
          (fun i : I.erase iStar => (Finset.univ : Finset (Fin (m i.1).length))) (H z')).symm
      _ ≤ C * ∏ _i : I.erase iStar, A := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.prod_le_prod₀
        · intro i hi
          exact Finset.sum_nonneg (fun k hk => hH z' i k)
        · intro i hi
          exact pd4c_hit_index_damping ρ hρ0 hρ1 (m i.1) z'
      _ = C * A ^ (I.erase iStar).card := by simp
      _ ≤ C * A ^ K := mul_le_mul_of_nonneg_left hpow hC
  by_cases hex : ∃ σ κ z', z' ∈ T ∧ W σ κ z' ≠ 0
  · obtain ⟨σ₀, κ₀, z₀, hz₀, hW₀⟩ := hex
    have href := hsupport σ₀ κ₀ z₀ hW₀
    let Z : Finset (ℤ × ℤ) :=
      T.filter (fun z' => envBox S w z' ∧ det2 z z' = det2 z z₀)
    have hZfinite : {z' : ℤ × ℤ | envBox S w z' ∧ det2 z z' = det2 z z₀}.Finite :=
      hfin.subset (fun z' hz' => hz'.1)
    have hZsub : (Z : Set (ℤ × ℤ)) ⊆
        {z' : ℤ × ℤ | envBox S w z' ∧ det2 z z' = det2 z z₀} := by
      intro z' hz'
      exact (Finset.mem_filter.mp hz').2
    have hZcard : (Z.card : ℝ) ≤ 34 := by
      calc
        _ ≤ ({z' : ℤ × ℤ | envBox S w z' ∧ det2 z z' = det2 z z₀}.ncard : ℝ) := by
          exact_mod_cast (by simpa using Set.ncard_le_ncard hZsub hZfinite)
        _ ≤ 34 := pd4c_env_fixed_det_count S w z (det2 z z₀) hU hw hz hbox
    have hzero (σ : Fin K → Equiv.Perm (Fin (slotCount S.x)))
        (κ : RawPromotionIndices I iStar m) (z' : ℤ × ℤ)
        (hz' : z' ∈ T) (hnot : z' ∉ Z) : W σ κ z' = 0 := by
      by_contra hne
      have hr := hsupport σ κ z' hne
      have hd := (raw_good_anchor_endpoint_unique S a p hp hbands I iStar fresh
        hfresh w e he hband hban z hz hU hw hbox hsep
        (fun i => σ i (lastSlot S.x)) (fun i => σ₀ i (lastSlot S.x))
        (rawPromotionLabels I iStar m κ) (rawPromotionLabels I iStar m κ₀)
        z' z₀ hr href).2.1
      obtain ⟨_, _, _, _, hbox', _, _⟩ := hr
      exact hnot (Finset.mem_filter.mpr ⟨hz', hbox', hd⟩)
    let V (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) : ℝ :=
      ∑ z' ∈ T, ∑ κ : RawPromotionIndices I iStar m, W σ κ z'
    have hVbound (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) : V σ ≤ 34 * C * A ^ K := by
      have hrestrict : V σ = ∑ z' ∈ Z, ∑ κ : RawPromotionIndices I iStar m, W σ κ z' := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro z' hz' hnot
        exact Finset.sum_eq_zero (fun κ hκ => hzero σ κ z' hz' hnot)
      calc
        _ = ∑ z' ∈ Z, ∑ κ : RawPromotionIndices I iStar m, W σ κ z' := hrestrict
        _ ≤ ∑ _z' ∈ Z, C * A ^ K := Finset.sum_le_sum (fun z' hz' => hindex σ z')
        _ = (Z.card : ℝ) * (C * A ^ K) := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 34 * (C * A ^ K) :=
          mul_le_mul_of_nonneg_right hZcard (mul_nonneg hC (pow_nonneg hA0 _))
        _ = _ := by ring
    have hVsupport (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) (hne : V σ ≠ 0) :
        RawAnchorCompatible S a p I iStar fresh w e z (fun i => σ i (lastSlot S.x)) := by
      by_contra hnot
      apply hne
      apply Finset.sum_eq_zero
      intro z' hz'
      apply Finset.sum_eq_zero
      intro κ hκ
      by_contra hne'
      exact hnot ⟨rawPromotionLabels I iStar m κ, z', hsupport σ κ z' hne'⟩
    simpa only [V, A] using raw_good_anchor_omission_average S a p
      (fun i j => (hp.1 i j).1) (pd4c_validPrimeLists_global_injective p hp hbands)
      I iStar fresh hfresh w e he hband hban z hz hU hw hbox hsep
      V (34 * C * A ^ K) (by positivity) hVbound hVsupport
  · have hzero (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
        (∑ z' ∈ T, ∑ κ : RawPromotionIndices I iStar m, W σ κ z') = 0 := by
      apply Finset.sum_eq_zero
      intro z' hz'
      apply Finset.sum_eq_zero
      intro κ hκ
      by_contra hne
      exact hex ⟨σ, κ, z', hz', hne⟩
    simp only [hzero, Finset.sum_const_zero, mul_zero]
    exact div_nonneg (by positivity) (pow_nonneg (Nat.cast_nonneg _) _)

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
