import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

/-- The modified prime density costs at most a factor two against the probability density. -/
theorem pd4c_memoryNu_le_twice_mu {K : ℕ} {x : ℝ} {a : Fin K → ℝ}
    (q : ℝ) (i : Fin K) (p : ℕ) (hp : 0 < p)
    (hV : 0 < bandMass x (a i)) (hb : (1 / 2 : ℝ) ≤ memoryBPrime x q p) :
    0 ≤ memoryNu x K a q i p ∧
      memoryNu x K a q i p ≤ 2 * (1 / (bandMass x (a i) * (p : ℝ))) := by
  have hpr : 0 < (p : ℝ) := by exact_mod_cast hp
  have hbp : 0 < memoryBPrime x q p := by linarith
  have hden : 0 < bandMass x (a i) * ((p : ℝ) + 1) * memoryBPrime x q p := by positivity
  constructor
  · exact (one_div_pos.mpr hden).le
  · unfold memoryNu
    rw [mul_one_div]
    apply (div_le_div_iff₀ hden (mul_pos hV hpr)).2
    have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ (p : ℝ) + 1 by positivity)
    have hb'' := mul_le_mul_of_nonneg_left hb' hV.le
    nlinarith

/-- Fresh choices form a finite set, including when some groups are prescribed to be one. -/
theorem pd4c_freshChoice_finite {K : ℕ} (x : ℝ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) : {fresh : Fin K → ℕ | IsFreshChoice x a I fresh}.Finite := by
  classical
  let T : Fin K → Finset ℕ := fun i => if i ∈ I then {1} else primeBand x (a i)
  have hfinite := Set.finite_range (fun g : (i : Fin K) → {p // p ∈ T i} =>
    fun i => (g i).1)
  apply hfinite.subset
  intro fresh hfresh
  refine ⟨fun i => ⟨fresh i, ?_⟩, rfl⟩
  by_cases hi : i ∈ I
  · simp [T, hi, hfresh.1 i hi]
  · simpa [T, hi] using hfresh.2 i hi

/-- The exponential exceptional bound in test (ii) transfers to the modified densities. -/
theorem pd4c_bad_fresh_nu_mass {K : ℕ} (x d₀ : ℝ) (a : Fin K → ℝ)
    (q : ℝ) (p : PrimeLists x K) (r : ℝ) (I : Finset (Fin K)) (hI : I.Nonempty)
    (hV : ∀ i, 0 < bandMass x (a i))
    (hb : ∀ i, ∀ t ∈ primeBand x (a i), (1 / 2 : ℝ) ≤ memoryBPrime x q t)
    (hgood : goodTestTwo x d₀ K a p r) :
    (∑' fresh : Fin K → ℕ,
      if IsFreshChoice x a I fresh ∧
        ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₁ ∧
          IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₂ ∧ n₁ ≠ n₂ ∧
          circleDistance (((n₁ : ℝ) - n₂) * r) ≤
            100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI)))
      then ∏ i : Fin K, if i ∉ I then memoryNu x K a q i (fresh i) else 1
      else 0) ≤
        (2 : ℝ) ^ K * Real.exp (-(1 / 4 : ℝ) * Real.rpow (Real.log x) (a (I.max' hI))) := by
  classical
  let bad (fresh : Fin K → ℕ) : Prop := IsFreshChoice x a I fresh ∧
    ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₁ ∧
      IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₂ ∧ n₁ ≠ n₂ ∧
      circleDistance (((n₁ : ℝ) - n₂) * r) ≤
        100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI)))
  let f (fresh : Fin K → ℕ) : ℝ := if bad fresh then
    ∏ i : Fin K, if i ∉ I then memoryNu x K a q i (fresh i) else 1 else 0
  let g (fresh : Fin K → ℕ) : ℝ := if bad fresh then freshChoiceWeight x a I fresh else 0
  have hfinite := pd4c_freshChoice_finite x a I
  have hfs : Summable f := by
    apply summable_of_hasFiniteSupport
    apply hfinite.subset
    intro fresh hne
    by_contra hnot
    have hbad : ¬ bad fresh := fun h => hnot h.1
    exact hne (by simp [f, hbad])
  have hgs : Summable g := by
    apply summable_of_hasFiniteSupport
    apply hfinite.subset
    intro fresh hne
    by_contra hnot
    have hbad : ¬ bad fresh := fun h => hnot h.1
    exact hne (by simp [g, hbad])
  have hpoint (fresh : Fin K → ℕ) : f fresh ≤ (2 : ℝ) ^ K * g fresh := by
    by_cases hbad : bad fresh
    · have hfresh := hbad.1
      have hnu (i : Fin K) (hi : i ∉ I) :=
        pd4c_memoryNu_le_twice_mu q i (fresh i)
          (Finset.mem_filter.mp (hfresh.2 i hi)).2.1.pos (hV i) (hb i _ (hfresh.2 i hi))
      have hprod :
          (∏ i : Fin K, if i ∉ I then memoryNu x K a q i (fresh i) else 1) ≤
            ∏ i : Fin K, 2 * (if i ∉ I then 1 / (bandMass x (a i) * (fresh i : ℝ)) else 1) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          by_cases hmem : i ∈ I
          · simp [hmem]
          · simpa [hmem] using (hnu i hmem).1
        · intro i hi
          by_cases hmem : i ∈ I
          · simp [hmem]
          · simpa [hmem, one_div, mul_inv_rev] using (hnu i hmem).2
      rw [Finset.prod_mul_distrib] at hprod
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        f, g, if_pos hbad, freshChoiceWeight, if_pos hfresh] using hprod
    · simp [f, g, hbad]
  have htest : (∑' fresh, g fresh) ≤
      Real.exp (-(1 / 4 : ℝ) * Real.rpow (Real.log x) (a (I.max' hI))) := hgood I hI
  calc
    _ = ∑' fresh, f fresh := rfl
    _ ≤ ∑' fresh, (2 : ℝ) ^ K * g fresh := hfs.tsum_le_tsum hpoint (hgs.mul_left _)
    _ = (2 : ℝ) ^ K * ∑' fresh, g fresh := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left htest (by positivity)

/-- The prime integration factor of a choice, before its two endpoint dampings. -/
def pd4c_choicePrimeWeight {K : ℕ} (F : PDFix K) (S : PDScale) (s : MemPoint S.x K)
    (i : Fin K) (c : EdgeChoice S.x F.a (s.2.2 i) i) : ℝ :=
  match c.2 with
  | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
  | Sum.inr p => memoryNu S.x K F.a F.q_d i p

/-- Fixing promoted groups makes the choice mass a product of the group masses. -/
theorem pd4c_promoted_choice_mass {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (I : Finset (Fin K)) :
    (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      if edgePromotedSet c = I then ∏ i : Fin K, pd4c_choicePrimeWeight F S s i (c i) else 0) =
        ∏ i : Fin K, 2 * (if i ∈ I then
          ((s.2.2 i).length : ℝ) * (bandMass S.x (F.a i))⁻¹
          else ∑ p : primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) := by
  let g (i : Fin K) (c : EdgeChoice S.x F.a (s.2.2 i) i) : ℝ :=
    if (c.2.isLeft = true ↔ i ∈ I) then pd4c_choicePrimeWeight F S s i c else 0
  have hpoint (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :
      (if edgePromotedSet c = I then ∏ i : Fin K, pd4c_choicePrimeWeight F S s i (c i) else 0) =
        ∏ i : Fin K, g i (c i) := by
    have hiff : edgePromotedSet c = I ↔ ∀ i, ((c i).2.isLeft = true ↔ i ∈ I) := by
      simp only [edgePromotedSet, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hiff]
    by_cases hall : ∀ i, ((c i).2.isLeft = true ↔ i ∈ I)
    · rw [if_pos hall]
      apply Finset.prod_congr rfl
      intro i hi
      exact (if_pos (hall i)).symm
    · rw [if_neg hall]
      symm
      obtain ⟨i, hi⟩ := not_forall.mp hall
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [g, hi])
  have hgroup (i : Fin K) :
      (∑ c : EdgeChoice S.x F.a (s.2.2 i) i, g i c) =
        2 * (if i ∈ I then ((s.2.2 i).length : ℝ) * (bandMass S.x (F.a i))⁻¹ else
          ∑ p : primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_sum_type]
    by_cases hi : i ∈ I <;> simp [g, pd4c_choicePrimeWeight, hi]
    <;> ring
  simp_rw [hpoint]
  rw [← Fintype.piFinset_univ]
  calc
    _ = ∏ i : Fin K, ∑ c : EdgeChoice S.x F.a (s.2.2 i) i, g i c := by
      simpa using (Finset.prod_univ_sum (fun i : Fin K => Finset.univ) g).symm
    _ = _ := by simp_rw [hgroup]

/-- A prescribed promotion pattern has at most a polynomial memory-cutoff cost. -/
theorem pd4c_promoted_choice_mass_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (I : Finset (Fin K)) (B C : ℝ)
    (hB : 1 ≤ B) (hC : 2 ≤ C)
    (hlen : ∀ i, ((s.2.2 i).length : ℝ) ≤ B)
    (hV : ∀ i, 0 < bandMass S.x (F.a i))
    (hVinv : ∀ i, (bandMass S.x (F.a i))⁻¹ ≤ C)
    (hν : ∀ i, ∀ p : primeBand S.x (F.a i), 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hνsum : ∀ i, (∑ p : primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ≤ 2) :
    (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      if edgePromotedSet c = I then ∏ i : Fin K, pd4c_choicePrimeWeight F S s i (c i) else 0) ≤
        (2 * C * B) ^ K := by
  rw [pd4c_promoted_choice_mass]
  have hBn : 0 ≤ B := by linarith
  have hCn : 0 ≤ C := by linarith
  calc
    _ ≤ ∏ i : Fin K, 2 * C * B := by
      apply Finset.prod_le_prod₀
      · intro i hi
        apply mul_nonneg (by norm_num)
        split_ifs
        · exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (hV i).le)
        · exact Finset.sum_nonneg fun p hp => hν i p
      · intro i hi
        by_cases hI : i ∈ I
        · simp only [if_pos hI]
          have h := mul_le_mul (hlen i) (hVinv i)
            (inv_nonneg.mpr (hV i).le) hBn
          nlinarith
        · simp only [if_neg hI]
          have hCB : 2 ≤ C * B := by
            calc
              _ ≤ C := hC
              _ ≤ C * B := by simpa using mul_le_mul_of_nonneg_left hB hCn
          nlinarith [hνsum i]
    _ = _ := by simp

end

end ArtinPrimitiveRoots.TypeII.PD
