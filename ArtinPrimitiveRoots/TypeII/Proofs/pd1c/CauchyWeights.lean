import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyPrimes

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII Filter
set_option maxHeartbeats 1000000

lemma pd1c_bandMass_uniform (K : ℕ) (a : Fin K → ℝ) (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ i : Fin K,
      Real.log 2 / 2 ≤ bandMass x (a i) ∧ bandMass x (a i) ≤ 2 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hex : ∀ i : Fin K, ∃ y₀ : ℝ, 2 ≤ y₀ ∧ ∀ x : ℝ, y₀ ≤ x →
      Real.log 2 / 2 ≤ bandMass x (a i) ∧ bandMass x (a i) ≤ 2 * Real.log 2 := by
    intro i
    obtain ⟨y₀, hy₀, hy⟩ := band_mass (a i) (by linarith [(ha.2.1 i).1])
      (by linarith [(ha.2.1 i).2]) (Real.log 2 / 2) (by positivity)
    refine ⟨y₀, hy₀, ?_⟩
    intro x hx
    obtain ⟨hm, hp⟩ := hy x hx
    rw [abs_le] at hm
    constructor <;> linarith
  choose y₀ hy₀ hy using hex
  let x₀ := 2 + ∑ i : Fin K, max 0 (y₀ i)
  have hs : 0 ≤ ∑ i : Fin K, max 0 (y₀ i) := Finset.sum_nonneg fun i hi => le_max_left _ _
  refine ⟨x₀, by dsimp [x₀]; linarith, ?_⟩
  intro x hx i
  apply hy i x
  have hi : max 0 (y₀ i) ≤ ∑ j : Fin K, max 0 (y₀ j) :=
    Finset.single_le_sum (fun j hj => le_max_left _ _) (Finset.mem_univ i)
  have : y₀ i ≤ x₀ := by dsimp [x₀]; linarith [le_max_right 0 (y₀ i)]
  exact this.trans hx

lemma pd1c_geometric_count_bound (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) * q ^ (n - 1) ≤ B := by
  obtain ⟨b, hb⟩ := (tendsto_self_mul_const_pow_of_lt_one hq₀.le hq₁).bddAbove_range
  refine ⟨(max 1 b) / q, by positivity, ?_⟩
  intro n hn
  have hbound : (n : ℝ) * q ^ n ≤ max 1 b :=
    (hb (Set.mem_range_self n)).trans (le_max_right _ _)
  have hnEq : n - 1 + 1 = n := by omega
  have hpow : q ^ n = q ^ (n - 1) * q := by
    calc
      q ^ n = q ^ (n - 1 + 1) := congrArg (fun j : ℕ => q ^ j) hnEq.symm
      _ = _ := pow_succ q (n - 1)
  apply (le_div_iff₀ hq₀).mpr
  simpa only [hpow, mul_assoc] using hbound

lemma pd1c_band_square_tail {x a : ℝ} :
    (∑ p ∈ primeBand x a, (1 / (p : ℝ)) ^ 2) ≤
      Real.exp (-Real.rpow (Real.log x) a) * bandMass x a := by
  unfold bandMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hmem := (Finset.mem_filter.mp hp).2
  have hpos : 0 < (p : ℝ) := by exact_mod_cast hmem.1.pos
  have hInv : 1 / (p : ℝ) ≤ Real.exp (-Real.rpow (Real.log x) a) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) hmem.2.1
  calc
    _ = (1 / (p : ℝ)) * (1 / (p : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hInv (by positivity)

lemma pd1c_all_band_square_tail {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (ha : ValidBands K a) (hL : 1 ≤ Real.log x)
    (hMass : ∀ i : Fin K, bandMass x (a i) ≤ 2 * Real.log 2) :
    (∑ i : Fin K, ∑ p ∈ primeBand x (a i), (1 / (p : ℝ)) ^ 2) ≤
      2 * K * Real.log 2 * Real.exp (-(Real.log x) ^ (1 / 10 : ℝ)) := by
  calc
    _ ≤ ∑ i : Fin K, Real.exp (-Real.rpow (Real.log x) (a i)) * bandMass x (a i) :=
      Finset.sum_le_sum fun i hi => pd1c_band_square_tail
    _ ≤ ∑ i : Fin K, Real.exp (-(Real.log x) ^ (1 / 10 : ℝ)) * (2 * Real.log 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have he : Real.exp (-Real.rpow (Real.log x) (a i)) ≤
          Real.exp (-(Real.log x) ^ (1 / 10 : ℝ)) :=
        Real.exp_le_exp.mpr (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hL (ha.2.1 i).1.le))
      exact mul_le_mul he (hMass i) (by unfold bandMass; positivity) (Real.exp_pos _).le
    _ = _ := by simp; ring

lemma pd1c_tuple_dvd_iff
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {t : Fin K → ℕ}
    (ht : IsMarkedPrimeTuple x K a t)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (z : ℕ) : tupleProduct t ∣ z ↔ ∀ i, t i ∣ z := by
  constructor
  · intro h i
    exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans h
  · intro h
    apply Fintype.prod_dvd_of_isRelPrime _ h
    intro i j hij
    apply Nat.coprime_iff_isRelPrime.mp
    apply (pd1c_tuple_entry_prime ht i).coprime_iff_not_dvd.mpr
    intro hd
    have heq : t i = t j := by
      rcases (Nat.dvd_prime (pd1c_tuple_entry_prime ht j)).mp hd with h1 | heq
      · exact ((pd1c_tuple_entry_prime ht i).ne_one h1).elim
      · exact heq
    exact Finset.disjoint_left.mp (hSep i j hij) (ht i) (by rw [heq]; exact ht j)

lemma pd1c_dividingTuple_card
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (z : ℕ) :
    ((pd1c_markedTupleSet x K a).filter (fun t => tupleProduct t ∣ z)).card =
      ∏ i : Fin K, bandOmega x (a i) z := by
  have heq : (pd1c_markedTupleSet x K a).filter (fun t => tupleProduct t ∣ z) =
      Fintype.piFinset (fun i : Fin K => (primeBand x (a i)).filter (fun p => p ∣ z)) := by
    ext t
    simp only [Finset.mem_filter, pd1c_markedTuple_mem, Fintype.mem_piFinset]
    constructor
    · rintro ⟨ht, hd⟩ i
      exact ⟨ht i, (pd1c_tuple_dvd_iff ht hSep z).mp hd i⟩
    · intro h
      have ht : IsMarkedPrimeTuple x K a t := fun i => (h i).1
      exact ⟨ht, (pd1c_tuple_dvd_iff ht hSep z).mpr (fun i => (h i).2)⟩
  rw [heq, Fintype.card_piFinset]
  rfl

lemma pd1c_markedWeight_nonneg {x q : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hq : 0 ≤ q) (hMass : ∀ i : Fin K, 0 ≤ bandMass x (a i)) (z : ℕ) :
    0 ≤ markedWeight x K a q z := by
  unfold markedWeight
  split_ifs
  · exact mul_nonneg (pow_nonneg hq _) (Finset.prod_nonneg (fun i hi => div_nonneg (Nat.cast_nonneg _) (hMass i)))
  · rfl

lemma pd1c_markedWeight_bound {x q v B : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hq : 0 ≤ q) (hv : 0 < v) (hB : 0 ≤ B)
    (hCount : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * q ^ (n - 1) ≤ B)
    (hMass : ∀ i : Fin K, v ≤ bandMass x (a i)) (z : ℕ) :
    markedWeight x K a q z ≤ (B / v) ^ K := by
  unfold markedWeight
  split_ifs with h
  · have hOne : ∀ i : Fin K, 1 ≤ bandOmega x (a i) z := by
      intro i
      obtain ⟨p, hp, hd⟩ := h i
      exact Finset.one_le_card.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hd⟩⟩
    have hExp : markedOmega x K a z - K = ∑ i : Fin K, (bandOmega x (a i) z - 1) := by
      rw [Finset.sum_tsub_distrib _ (fun i hi => hOne i)]
      simp [markedOmega]
    rw [hExp, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    calc
      _ ≤ ∏ i : Fin K, B / v := by
        apply Finset.prod_le_prod₀
        · intro i hi
          have hMi := hv.trans_le (hMass i)
          positivity
        · intro i hi
          calc
            q ^ (bandOmega x (a i) z - 1) * ((bandOmega x (a i) z : ℝ) / bandMass x (a i)) =
                ((bandOmega x (a i) z : ℝ) * q ^ (bandOmega x (a i) z - 1)) / bandMass x (a i) := by ring
            _ ≤ B / v := div_le_div₀ hB (hCount _ (hOne i)) hv (hMass i)
      _ = _ := by rw [Finset.prod_const]; simp
  · positivity

lemma pd1c_markedWeight_tuple_expansion {x q : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (z : ℕ) :
    markedWeight x K a q z =
      (∏ i : Fin K, (bandMass x (a i))⁻¹) *
        ∑ t ∈ pd1c_markedTupleSet x K a,
          if tupleProduct t ∣ z then q ^ (markedOmega x K a z - K) else 0 := by
  have hsum : (∑ t ∈ pd1c_markedTupleSet x K a,
      if tupleProduct t ∣ z then q ^ (markedOmega x K a z - K) else 0) =
      (∏ i : Fin K, (bandOmega x (a i) z : ℝ)) * q ^ (markedOmega x K a z - K) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, pd1c_dividingTuple_card hSep z, Nat.cast_prod]
  rw [hsum]
  unfold markedWeight
  by_cases h : ∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ z
  · rw [if_pos h]
    simp only [div_eq_mul_inv, Finset.prod_mul_distrib]
    ring
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    have hz : bandOmega x (a i) z = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hi ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    have hprod : (∏ i : Fin K, (bandOmega x (a i) z : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hz])
    simp [hprod]

noncomputable def pd1c_replacedWeight (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (q : ℝ) (z : ℕ) : ℝ :=
  (∏ i : Fin K, (bandMass x (a i))⁻¹) *
    ∑ t ∈ pd1c_markedTupleSet x K a,
      if tupleProduct t ∣ z then q ^ markedOmega x K a (z / tupleProduct t) else 0

lemma pd1c_replacedWeight_bounds {x q : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hMass : ∀ i : Fin K, 0 ≤ bandMass x (a i))
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (z : ℕ) : 0 ≤ pd1c_replacedWeight x K a q z ∧
      pd1c_replacedWeight x K a q z ≤ markedWeight x K a q z := by
  have hn : 0 ≤ ∏ i : Fin K, (bandMass x (a i))⁻¹ :=
    Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (hMass i))
  constructor
  · unfold pd1c_replacedWeight
    exact mul_nonneg hn (Finset.sum_nonneg (fun t ht => by split_ifs <;> positivity))
  · rw [pd1c_markedWeight_tuple_expansion hSep z]
    unfold pd1c_replacedWeight
    apply mul_le_mul_of_nonneg_left _ hn
    apply Finset.sum_le_sum
    intro t ht
    by_cases hd : tupleProduct t ∣ z
    · rw [if_pos hd, if_pos hd]
      have hrec : tupleProduct t * (z / tupleProduct t) = z := Nat.mul_div_cancel' hd
      have hOm := (pd1c_markedOmega_mul_tuple_le ((pd1c_markedTuple_mem _ _ _ _).mp ht)
        hSep (z / tupleProduct t)).2
      rw [hrec] at hOm
      exact pow_le_pow_of_le_one hq₀ hq₁ (by omega : markedOmega x K a z - K ≤ markedOmega x K a (z / tupleProduct t))
    · simp [hd]

lemma pd1c_replacedWeight_eq_of_no_square {x q : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (z : ℕ) (hSquare : ∀ p ∈ markedPrimes x K a, ¬p ^ 2 ∣ z) :
    pd1c_replacedWeight x K a q z = markedWeight x K a q z := by
  rw [pd1c_markedWeight_tuple_expansion hSep z]
  unfold pd1c_replacedWeight
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hd : tupleProduct t ∣ z
  · rw [if_pos hd, if_pos hd]
    have hrec : tupleProduct t * (z / tupleProduct t) = z := Nat.mul_div_cancel' hd
    have ht' := (pd1c_markedTuple_mem _ _ _ _).mp ht
    have hnot : ∀ i : Fin K, ¬t i ∣ z / tupleProduct t := by
      intro i hi
      have hm : t i ∈ markedPrimes x K a := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ht' i⟩
      apply hSquare (t i) hm
      rw [← hrec, pow_two]
      exact mul_dvd_mul (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) hi
    have hOm := pd1c_markedOmega_mul_tuple_eq ht' hSep (z / tupleProduct t) hnot
    rw [hrec] at hOm
    congr 1
    omega
  · simp [hd]

end ArtinPrimitiveRoots.TypeII.PD
