import ArtinPrimitiveRoots.Construction.Defs

namespace ArtinPrimitiveRoots.Construction.Proofs.C_BINS

open Classical ArtinPrimitiveRoots.TypeII
open MeasureTheory

theorem roughDensityTerm_nonneg (γ w : ℝ) (hγ : 0 < γ) (hγw : γ < w) (j : ℕ) :
    0 ≤ ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j := by
  rw [ArtinPrimitiveRoots.Sieve.roughDensityTerm]
  split_ifs with hj0 hj1
  · norm_num
  · have hw : 0 < w := by linarith
    positivity
  · apply mul_nonneg
    · exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
    · apply integral_nonneg
      intro t
      by_cases ht : (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ
      · simp [Set.indicator, ht]
        apply mul_nonneg
        · apply inv_nonneg.mpr
          have hsum := ht.2
          linarith
        · apply inv_nonneg.mpr
          apply Finset.prod_nonneg
          intro i hi
          have hi' := ht.1 i
          linarith
      · simp [Set.indicator, ht]

theorem roughDensity_nonneg (γ w : ℝ) (hγ : 0 < γ) (hγw : γ < w) :
    0 ≤ ArtinPrimitiveRoots.Sieve.roughDensity γ w := by
  unfold ArtinPrimitiveRoots.Sieve.roughDensity
  apply tsum_nonneg
  intro j
  exact roughDensityTerm_nonneg γ w hγ hγw j

theorem roughDensityBinSup_nonneg (γ γ' : ℝ) (hγ : 0 < γ)
    (hγγ' : γ ≤ γ') (hγw : γ < 1 - γ) :
    0 ≤ sSup ((fun t : ℝ => ArtinPrimitiveRoots.Sieve.roughDensity γ (1 - t)) ''
      Set.Icc γ γ') := by
  let S : Set ℝ := (fun t : ℝ => ArtinPrimitiveRoots.Sieve.roughDensity γ (1 - t)) ''
    Set.Icc γ γ'
  have hmem : ArtinPrimitiveRoots.Sieve.roughDensity γ (1 - γ) ∈ S := by
    exact ⟨γ, ⟨le_rfl, hγγ'⟩, rfl⟩
  have hval : 0 ≤ ArtinPrimitiveRoots.Sieve.roughDensity γ (1 - γ) :=
    roughDensity_nonneg γ (1 - γ) hγ hγw
  by_cases hbdd : BddAbove S
  · exact hval.trans (le_csSup hbdd hmem)
  · rw [csSup_of_not_bddAbove hbdd]
    simp

theorem roughSieveProduct_nonneg (y : ℝ) :
    0 ≤ ArtinPrimitiveRoots.TypeII.roughSieveProduct y := by
  unfold ArtinPrimitiveRoots.TypeII.roughSieveProduct
  apply Finset.prod_nonneg
  intro p hp
  have hp' : p.Prime := by
    dsimp [ArtinPrimitiveRoots.TypeII.primesUpTo] at hp
    exact (Finset.mem_filter.mp hp).2
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp'.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.one_le
  rw [sub_nonneg]
  exact (div_le_one₀ hp0).2 hp1

theorem roughAbove_iff_avoids_primesUpTo (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    roughAbove n y ↔ ∀ p ∈ primesUpTo y, ¬ p ∣ n := by
  constructor
  · intro hr p hp hpdiv
    have hp' : p.Prime := by
      dsimp [primesUpTo] at hp
      exact (Finset.mem_filter.mp hp).2
    have hple : (p : ℝ) ≤ y := by
      have hpNat : p ≤ ⌊y⌋₊ := by
        dsimp [primesUpTo] at hp
        have hpRange : p < ⌊y⌋₊ + 1 := by
          simpa only [Finset.mem_range] using (Finset.mem_filter.mp hp).1
        omega
      exact (Nat.cast_le.mpr hpNat).trans (Nat.floor_le hy)
    exact (not_lt_of_ge hple) (hr p hp' hpdiv)
  · intro h p hp hpdiv
    by_contra hnot
    have hple : (p : ℝ) ≤ y := le_of_not_gt hnot
    have hpNat : p ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy).2 hple
    have hpMem : p ∈ primesUpTo y := by
      dsimp [primesUpTo]
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp⟩
    exact h p hpMem hpdiv

theorem roughAbove_mul_iff (m n : ℕ) (y : ℝ) :
    roughAbove (m * n) y ↔ roughAbove m y ∧ roughAbove n y := by
  constructor
  · intro h
    constructor
    · intro p hp hpdiv
      exact h p hp (dvd_mul_of_dvd_left hpdiv n)
    · intro p hp hpdiv
      exact h p hp (dvd_mul_of_dvd_right hpdiv m)
  · rintro ⟨hm, hn⟩ p hp hpdiv
    rcases hp.dvd_mul.mp hpdiv with hpM | hpN
    · exact hm p hp hpM
    · exact hn p hp hpN

theorem markedPart_odd_of_two_not_marked (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (h : ℕ) (h₂ : 2 ∉ markedPrimes x K a) : Odd (markedPart x K a h) := by
  classical
  have hprod : ∀ s : Finset ℕ, (∀ p ∈ s, Odd p) →
      Odd (∏ p ∈ s, p ^ padicValNat p h) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro; simp
    | @insert p s hps ih =>
        intro hs
        rw [Finset.prod_insert hps]
        have hpOdd := hs p (Finset.mem_insert_self p s)
        have hs' : ∀ q ∈ s, Odd q := fun q hq => hs q (Finset.mem_insert_of_mem hq)
        exact (hpOdd.pow (n := padicValNat p h)).mul (ih hs')
  apply hprod
  intro p hp
  have hpPrime : p.Prime := by
    change p ∈ Finset.univ.biUnion (fun i => primeBand x (a i)) at hp
    rcases Finset.mem_biUnion.mp hp with ⟨i, _, hpi⟩
    dsimp [primeBand] at hpi
    exact (Finset.mem_filter.mp hpi).2.1
  have hpne : p ≠ 2 := by
    intro heq
    subst p
    exact h₂ hp
  have hpTwo : 2 ≤ p := hpPrime.two_le
  have hp3 : 3 ≤ p := by omega
  exact hpPrime.odd_iff.mpr hp3

private theorem bandMass_nonneg (x a : ℝ) : 0 ≤ bandMass x a := by
  unfold bandMass
  apply Finset.sum_nonneg
  intro p hp
  have hp' : p.Prime := by
    dsimp [primeBand] at hp
    exact (Finset.mem_filter.mp hp).2.1
  positivity

theorem markedWeight_nonneg (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (q : ℝ) (h : ℕ)
    (hq : 0 ≤ q) :
    0 ≤ markedWeight x K a q h := by
  unfold markedWeight
  split
  · apply mul_nonneg
    · exact pow_nonneg hq _
    · apply Finset.prod_nonneg
      intro i hi
      apply div_nonneg
      · exact Nat.cast_nonneg _
      · exact bandMass_nonneg x (a i)
  · exact le_of_eq rfl

theorem markedWeight_mul_eq_of_no_marked_prime (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (q : ℝ) (s h : ℕ)
    (hs : ∀ p ∈ markedPrimes x K a, ¬ p ∣ s) :
    markedWeight x K a q (s * h) = markedWeight x K a q h := by
  classical
  have hband : ∀ i : Fin K, bandOmega x (a i) (s * h) = bandOmega x (a i) h := by
    intro i
    unfold bandOmega
    congr 1
    apply Finset.filter_congr
    intro p hp
    have hpPrime : p.Prime := by
      dsimp [primeBand] at hp
      exact (Finset.mem_filter.mp hp).2.1
    have hpMarked : p ∈ markedPrimes x K a := by
      change p ∈ Finset.univ.biUnion (fun j => primeBand x (a j))
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩
    have hpdvd : p ∣ s * h ↔ p ∣ h := by
      rw [hpPrime.dvd_mul]
      simp [hs p hpMarked]
    exact hpdvd
  have hOmega : markedOmega x K a (s * h) = markedOmega x K a h := by
    unfold markedOmega
    apply Finset.sum_congr rfl
    intro i hi
    exact hband i
  have hcond :
      (∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ s * h) ↔
      (∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ h) := by
    constructor
    · intro hall i
      rcases hall i with ⟨p, hp, hpdvd⟩
      have hpPrime : p.Prime := by
        dsimp [primeBand] at hp
        exact (Finset.mem_filter.mp hp).2.1
      have hpMarked : p ∈ markedPrimes x K a := by
        change p ∈ Finset.univ.biUnion (fun j => primeBand x (a j))
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩
      rcases hpPrime.dvd_mul.mp hpdvd with hps | hph
      · exact False.elim (hs p hpMarked hps)
      · exact ⟨p, hp, hph⟩
    · intro hall i
      rcases hall i with ⟨p, hp, hpdvd⟩
      exact ⟨p, hp, dvd_mul_of_dvd_right hpdvd s⟩
  by_cases hc : ∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ s * h
  · have hc' := hcond.mp hc
    simp [markedWeight, hc, hc', hOmega, hband]
  · have hc' : ¬ ∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ h := by
      intro hh
      exact hc (hcond.mpr hh)
    simp [markedWeight, hc, hc']

theorem conFactor_nonneg (x : ℝ) (c K : ℕ) (a : Fin K → ℝ) (h : ℕ) :
    0 ≤ conFactor x c K a h := by
  unfold conFactor
  split <;> norm_num

theorem conWeight_nonneg (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) (hΨ : IsTestFunction Ψ) (d : ℕ) :
    0 ≤ conWeight x M c u K a Ψ d := by
  unfold conWeight
  split
  · exact mul_nonneg (mul_nonneg (hΨ.2.2.1 _) (conFactor_nonneg x c K a (d - 1)))
      (markedWeight_nonneg x K a (1 / 2 : ℝ) (d - 1) (by norm_num))
  · exact le_of_eq rfl

theorem conTotalMass_nonneg (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) (hΨ : IsTestFunction Ψ) :
    0 ≤ conTotalMass x M c u K a Ψ := by
  unfold conTotalMass
  apply Finset.sum_nonneg
  intro d hd
  exact conWeight_nonneg x M c u K a Ψ hΨ d

theorem testFunction_ne_zero_bounds (Ψ : ℝ → ℝ) (hΨ : IsTestFunction Ψ) (y : ℝ)
    (hy : Ψ y ≠ 0) : 1 < y ∧ y < 2 := by
  have hySupport : y ∈ Function.support Ψ := by
    simpa [Function.mem_support] using hy
  exact hΨ.2.1 hySupport

theorem pairWeight_ne_zero_bounds (x : ℝ) (c K : ℕ) (a : Fin K → ℝ)
    (r Q : ℕ) (Ψ : ℝ → ℝ)
    (hΨ : IsTestFunction Ψ) (hx : 0 < x)
    (h : Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) *
      markedWeight x K a (1 / 2 : ℝ) r ≠ 0) :
    x < ((c * r * Q + 1 : ℕ) : ℝ) ∧ ((c * r * Q + 1 : ℕ) : ℝ) < 2 * x := by
  have hΨne : Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) ≠ 0 := by
    intro hzero
    apply h
    exact mul_eq_zero.mpr (Or.inl hzero)
  have hIoo := testFunction_ne_zero_bounds Ψ hΨ _ hΨne
  constructor
  · simpa using (lt_div_iff₀ hx).mp hIoo.1
  · exact (div_lt_iff₀ hx).mp hIoo.2

theorem conWeight_ne_zero_bounds (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) (hΨ : IsTestFunction Ψ) (d : ℕ)
    (hd : conWeight x M c u K a Ψ d ≠ 0) :
    x < (d : ℝ) ∧ (d : ℝ) < 2 * x := by
  have hcond : 1 < d ∧ (d : ℤ) ≡ u [ZMOD M] := by
    by_contra h
    simp [conWeight, h] at hd
  have hpsi : Ψ ((d : ℝ) / x) ≠ 0 := by
    intro hzero
    apply hd
    simp [conWeight, hcond, hzero]
  have hsupport : (d : ℝ) / x ∈ Function.support Ψ := by
    simpa [Function.mem_support] using hpsi
  have hsupp : (d : ℝ) / x ∈ Set.Ioo (1 : ℝ) 2 := hΨ.2.1 hsupport
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (show 0 < d by omega)
  have hx : 0 < x := by
    by_contra hx
    have hxle : x ≤ 0 := le_of_not_gt hx
    have hdiv : (d : ℝ) / x ≤ 0 := div_nonpos_of_nonneg_of_nonpos hdpos.le hxle
    linarith [hsupp.1]
  constructor
  · have hmul : (1 : ℝ) * x < (d : ℝ) := (lt_div_iff₀ hx).mp hsupp.1
    simpa using hmul
  · exact (div_lt_iff₀ hx).mp hsupp.2

theorem conWeight_ne_zero_factor (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) (d : ℕ)
    (hd : conWeight x M c u K a Ψ d ≠ 0) :
    ∃ Q : ℕ, Q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
      d - 1 = c * markedPart x K a (d - 1) * Q := by
  have hcond : 1 < d ∧ (d : ℤ) ≡ u [ZMOD M] := by
    by_contra h
    simp [conWeight, h] at hd
  have hfac : conFactor x c K a (d - 1) ≠ 0 := by
    intro hzero
    apply hd
    simp [conWeight, hcond, hzero]
  simpa [conFactor] using hfac

theorem largePrimeFactorization_unique (x : ℝ) (c h r₁ r₂ Q₁ Q₂ : ℕ)
    (hx : 1 < x) (hc : 0 < c) (hQ₁ : Q₁.Prime) (hQ₂ : Q₂.Prime)
    (hr₂ : (r₂ : ℝ) ≤ Real.rpow x (11 / 100 : ℝ))
    (hlarge₁ : Real.rpow x (9 / 10 : ℝ) < (Q₁ : ℝ))
    (hpos : 0 < h)
    (hfact₁ : h = c * r₁ * Q₁) (hfact₂ : h = c * r₂ * Q₂) :
    r₁ = r₂ ∧ Q₁ = Q₂ := by
  have hpow : Real.rpow x (11 / 100 : ℝ) < Real.rpow x (9 / 10 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hx (by norm_num)
  have hr₂Q₁ : r₂ < Q₁ := by
    exact_mod_cast (lt_trans (lt_of_le_of_lt hr₂ hpow) hlarge₁)
  have hr₂pos : 0 < r₂ := by
    by_contra hnot
    have hr₂zero : r₂ = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hr₂zero] at hfact₂
    simp at hfact₂
    omega
  have hprod₁ : c * (r₁ * Q₁) = h := by
    simpa [Nat.mul_assoc] using hfact₁.symm
  have hprod₂ : c * (r₂ * Q₂) = h := by
    simpa [Nat.mul_assoc] using hfact₂.symm
  have hprod : r₁ * Q₁ = r₂ * Q₂ :=
    Nat.mul_left_cancel hc (hprod₁.trans hprod₂.symm)
  have hQ₁div : Q₁ ∣ r₂ * Q₂ := by
    rw [← hprod]
    exact dvd_mul_of_dvd_right (dvd_rfl : Q₁ ∣ Q₁) r₁
  rcases hQ₁.dvd_mul.mp hQ₁div with hQ₁r₂ | hQ₁Q₂
  · exact False.elim ((Nat.not_dvd_of_pos_of_lt hr₂pos hr₂Q₁) hQ₁r₂)
  · have hQeq : Q₁ = Q₂ := by
      rcases hQ₂.eq_one_or_self_of_dvd Q₁ hQ₁Q₂ with hone | heq
      · exact (hQ₁.ne_one hone).elim
      · exact heq
    refine ⟨?_, hQeq⟩
    exact Nat.mul_right_cancel hQ₁.pos (by simpa [hQeq] using hprod)

theorem markedPart_eq_self_of_groupInteger (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (r : ℕ) (hr : IsGroupInteger x K a r) (hrpos : 0 < r) :
    markedPart x K a r = r := by
  have hsubset : r.factorization.support ⊆ markedPrimes x K a := by
    intro p hp
    have hmem : p ∈ r.primeFactors := by
      simpa [Nat.support_factorization] using hp
    rcases Nat.mem_primeFactors.mp hmem with ⟨hpPrime, hpdiv, _⟩
    exact hr p hpPrime hpdiv
  unfold markedPart
  calc
    (∏ p ∈ markedPrimes x K a, p ^ padicValNat p r) =
        ∏ p ∈ r.factorization.support, p ^ padicValNat p r := by
      symm
      apply Finset.prod_subset hsubset
      intro p hpMark hpnotsupp
      have hpPrime : p.Prime := by
        dsimp [markedPrimes] at hpMark
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hpMark
        obtain ⟨i, hi⟩ := hpMark
        dsimp [primeBand] at hi
        exact (Finset.mem_filter.mp hi).2.1
      have hzero : padicValNat p r = 0 := by
        rw [← Nat.factorization_def r hpPrime]
        exact Finsupp.notMem_support_iff.mp hpnotsupp
      simp [hzero]
    _ = r.factorization.prod (fun p k => p ^ k) := by
      rw [Finsupp.prod]
      apply Finset.prod_congr rfl
      intro p hp
      have hmem : p ∈ r.primeFactors := by
        simpa [Nat.support_factorization] using hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hmem
      rw [Nat.factorization_def r hpPrime]
    _ = r := Nat.prod_factorization_pow_eq_self hrpos.ne'

theorem markedPart_mul_groupInteger (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (c r Q : ℕ) (hr : IsGroupInteger x K a r) (hcpos : 0 < c)
    (hrpos : 0 < r) (hQ : Q.Prime)
    (hcmarked : ∀ p ∈ markedPrimes x K a, ¬ p ∣ c)
    (hQmarked : ∀ p ∈ markedPrimes x K a, ¬ p ∣ Q) :
    markedPart x K a (c * r * Q) = r := by
  have hcne : c ≠ 0 := hcpos.ne'
  have hrne : r ≠ 0 := hrpos.ne'
  have hQne : Q ≠ 0 := hQ.ne_zero
  have hsubset : r.factorization.support ⊆ markedPrimes x K a := by
    intro p hp
    have hmem : p ∈ r.primeFactors := by
      simpa [Nat.support_factorization] using hp
    rcases Nat.mem_primeFactors.mp hmem with ⟨hpPrime, hpdiv, _⟩
    exact hr p hpPrime hpdiv
  have hmul : (c * r * Q).factorization = c.factorization + r.factorization + Q.factorization := by
    simp [Nat.factorization_mul, hcne, hrne, hQne, Nat.mul_assoc, add_assoc]
  have hexp (p : ℕ) (hp : p ∈ markedPrimes x K a) :
      padicValNat p (c * r * Q) = r.factorization p := by
    have hpPrime : p.Prime := by
      dsimp [markedPrimes] at hp
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
      obtain ⟨i, hi⟩ := hp
      dsimp [primeBand] at hi
      exact (Finset.mem_filter.mp hi).2.1
    have hcfac : c.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hmem
      have hprimeDiv : p ∣ c := (Nat.mem_primeFactors.mp (by simpa [Nat.support_factorization] using hmem)).2.1
      exact hcmarked p hp hprimeDiv
    have hQfac : Q.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hmem
      have hprimeDiv : p ∣ Q := (Nat.mem_primeFactors.mp (by simpa [Nat.support_factorization] using hmem)).2.1
      exact hQmarked p hp hprimeDiv
    rw [← Nat.factorization_def (c * r * Q) hpPrime, hmul]
    simp [Finsupp.add_apply, hcfac, hQfac, Nat.factorization_def r hpPrime]
  unfold markedPart
  calc
    (∏ p ∈ markedPrimes x K a, p ^ padicValNat p (c * r * Q)) =
        ∏ p ∈ markedPrimes x K a, p ^ r.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [hexp p hp]
    _ = r.factorization.prod (fun p k => p ^ k) := by
      rw [Finsupp.prod]
      symm
      apply Finset.prod_subset hsubset
      intro p hpMark hpnotsupp
      have hzero : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hpnotsupp
      simp [hzero]
    _ = r := Nat.prod_factorization_pow_eq_self hrne

theorem conWeight_eq_pair_weight (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) (r Q : ℕ) (hr : IsGroupInteger x K a r)
    (hcpos : 0 < c) (hrpos : 0 < r) (hQ : Q.Prime)
    (hlarge : Real.rpow x (9 / 10 : ℝ) < (Q : ℝ))
    (hcmarked : ∀ p ∈ markedPrimes x K a, ¬ p ∣ c)
    (hQmarked : ∀ p ∈ markedPrimes x K a, ¬ p ∣ Q)
    (hres : ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) :
    conWeight x M c u K a Ψ (c * r * Q + 1) =
      Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) *
        markedWeight x K a (1 / 2 : ℝ) r := by
  have hpart : markedPart x K a (c * r * Q) = r :=
    markedPart_mul_groupInteger x K a c r Q hr hcpos hrpos hQ hcmarked hQmarked
  have hsmarked : ∀ p ∈ markedPrimes x K a, ¬ p ∣ c * Q := by
    intro p hp hdiv
    have hpPrime : p.Prime := by
      change p ∈ Finset.univ.biUnion (fun j => primeBand x (a j)) at hp
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
      obtain ⟨i, hi⟩ := hp
      dsimp [primeBand] at hi
      exact (Finset.mem_filter.mp hi).2.1
    rcases hpPrime.dvd_mul.mp hdiv with hpc | hpQ
    · exact hcmarked p hp hpc
    · exact hQmarked p hp hpQ
  have hwt : markedWeight x K a (1 / 2 : ℝ) (c * r * Q) =
      markedWeight x K a (1 / 2 : ℝ) r := by
    simpa [Nat.mul_assoc, Nat.mul_comm Q r] using
      (markedWeight_mul_eq_of_no_marked_prime x K a (1 / 2 : ℝ) (c * Q) r hsmarked)
  have hsub : c * r * Q + 1 - 1 = c * r * Q := by omega
  have hdpos : 1 < c * r * Q + 1 := by
    have hprodpos : 0 < c * r * Q := Nat.mul_pos (Nat.mul_pos hcpos hrpos) hQ.pos
    omega
  have hqdata : ∃ Q' : ℕ, Q'.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q' : ℝ) ∧
      c * r * Q = c * markedPart x K a (c * r * Q) * Q' := by
    refine ⟨Q, hQ, hlarge, ?_⟩
    rw [hpart]
  have hfactor : conFactor x c K a (c * r * Q) = 1 := by
    unfold conFactor
    rw [if_pos hqdata]
  unfold conWeight
  rw [if_pos ⟨hdpos, hres⟩]
  rw [hsub, hfactor, hwt]
  simp

theorem primeBands_disjoint_large (K : ℕ) (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)) := by
  have hdis (i j : Fin K) (hij : a i < a j) :
      ∀ᶠ x : ℝ in Filter.atTop,
        Disjoint (primeBand x (a i)) (primeBand x (a j)) := by
    let δ := a j - a i
    have hδ : 0 < δ := sub_pos.mpr hij
    have hpow : Filter.Tendsto (fun x : ℝ => Real.rpow (Real.log x) δ)
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hδ).comp Real.tendsto_log_atTop
    have hlarge := hpow.eventually_gt_atTop 2
    have hlog : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.log x := by
      filter_upwards [Filter.eventually_atTop.2 ⟨Real.exp 1,
        fun x hx => by
          have h1exp : (1 : ℝ) < Real.exp 1 := by
            simpa using (Real.exp_strictMono (by norm_num : (0 : ℝ) < 1))
          have h1x : (1 : ℝ) < x := lt_of_lt_of_le h1exp hx
          exact Real.log_pos h1x⟩] with x hx
      exact hx
    filter_upwards [hlarge, hlog] with x hxlarge hxlog
    have hfactor : Real.rpow (Real.log x) (a j) =
        Real.rpow (Real.log x) (a i) * Real.rpow (Real.log x) δ := by
      calc
        Real.rpow (Real.log x) (a j) =
            Real.rpow (Real.log x) (a i + δ) := by
              congr 1
              dsimp [δ]
              ring
        _ = Real.rpow (Real.log x) (a i) * Real.rpow (Real.log x) δ :=
          Real.rpow_add hxlog _ _
    have hsep : 2 * Real.rpow (Real.log x) (a i) <
        Real.rpow (Real.log x) (a j) := by
      have hpos : 0 < Real.rpow (Real.log x) (a i) := Real.rpow_pos_of_pos hxlog _
      have hmult := mul_lt_mul_of_pos_left hxlarge hpos
      rw [hfactor]
      simpa [mul_comm] using hmult
    have hexp : Real.exp (2 * Real.rpow (Real.log x) (a i)) <
        Real.exp (Real.rpow (Real.log x) (a j)) := Real.exp_lt_exp.mpr hsep
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hpi' := hpi
    have hpj' := hpj
    dsimp [primeBand] at hpi' hpj'
    rcases Finset.mem_filter.mp hpi' with ⟨_, ⟨_, _, hupper⟩⟩
    rcases Finset.mem_filter.mp hpj' with ⟨_, ⟨_, hlower, _⟩⟩
    have hpupper : (p : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) (a i)) := hupper
    have hplower : Real.exp (Real.rpow (Real.log x) (a j)) ≤ (p : ℝ) := hlower
    linarith
  have hpair (i j : Fin K) (hij : i ≠ j) :
      ∀ᶠ x : ℝ in Filter.atTop,
        Disjoint (primeBand x (a i)) (primeBand x (a j)) := by
    have hlt : a i < a j ∨ a j < a i := by
      by_cases hval : i.val < j.val
      · exact Or.inl (ha.2.2 i j hval)
      · have hval' : j.val < i.val := by omega
        exact Or.inr (ha.2.2 j i hval')
    rcases hlt with hlt | hlt
    · exact hdis i j hlt
    · exact (hdis j i hlt).mono fun x h => h.symm
  have hall : ∀ᶠ x : ℝ in Filter.atTop,
      ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)) := by
    apply Filter.eventually_all.2
    intro i
    apply Filter.eventually_all.2
    intro j
    by_cases hij : i = j
    · subst j
      filter_upwards [] with x
      exact fun h => False.elim (h rfl)
    · filter_upwards [hpair i j hij] with x hx
      exact fun _ => hx
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hall
  exact ⟨x₀, hx₀⟩

private theorem markedWeight_onePrimeChoice (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (f : Fin K → ℕ)
    (hf : f ∈ Fintype.piFinset (fun i : Fin K => primeBand x (a i)))
    (hbands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    markedWeight x K a (1 / 2 : ℝ) (∏ i : Fin K, f i) =
      ∏ i : Fin K, 1 / bandMass x (a i) := by
  classical
  let B : Fin K → Finset ℕ := fun i => primeBand x (a i)
  let r : ℕ := ∏ i : Fin K, f i
  have hfi (i : Fin K) : f i ∈ B i := by
    exact Fintype.mem_piFinset.mp hf i
  have hprime (i : Fin K) : (f i).Prime := by
    dsimp [B, primeBand] at hfi
    exact (Finset.mem_filter.mp (hfi i)).2.1
  have hfactor (i : Fin K) (p : ℕ) (hp : p ∈ B i) (hpd : p ∣ r) :
      ∃ j : Fin K, p = f j := by
    have hpp : p.Prime := by
      dsimp [B, primeBand] at hp
      exact (Finset.mem_filter.mp hp).2.1
    obtain ⟨j, _, hdiv⟩ :=
      (_root_.Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hpp) f).mp hpd
    exact ⟨j, (Nat.prime_dvd_prime_iff_eq hpp (hprime j)).mp hdiv⟩
  have hfilter (i : Fin K) :
      (B i).filter (fun p => p ∣ r) = {f i} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hpd⟩
      obtain ⟨j, hpj⟩ := hfactor i p hp hpd
      by_cases hji : j = i
      · simpa [hji] using hpj
      · have hmemj : p ∈ B j := by rw [hpj]; exact hfi j
        have hdis := hbands i j (Ne.symm hji)
        exact False.elim ((Finset.disjoint_left.mp hdis) hp hmemj)
    · intro hp
      subst p
      refine ⟨hfi i, ?_⟩
      exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have hbandOmega (i : Fin K) : bandOmega x (a i) r = 1 := by
    unfold bandOmega
    change ((B i).filter (fun p => p ∣ r)).card = 1
    rw [hfilter i]
    simp
  have hSupport : ∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ r := by
    intro i
    refine ⟨f i, hfi i, ?_⟩
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have hOmega : markedOmega x K a r = K := by
    unfold markedOmega
    simp [hbandOmega]
  change markedWeight x K a (1 / 2 : ℝ) r = ∏ i : Fin K, 1 / bandMass x (a i)
  unfold markedWeight
  rw [if_pos hSupport]
  simp [hOmega, hbandOmega]

theorem markedPrimes_avoid_fixed_and_large (K : ℕ) (a : Fin K → ℝ)
    (ha : ValidBands K a) (c : ℕ) (hc : 0 < c) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (∀ p ∈ markedPrimes x K a, ¬ p ∣ c) ∧
      ∀ Q : ℕ, Q.Prime → Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) →
        ∀ p ∈ markedPrimes x K a, ¬ p ∣ Q := by
  have htend : Filter.Tendsto
      (fun x : ℝ => Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)))
      Filter.atTop Filter.atTop := by
    exact Real.tendsto_exp_atTop.comp
      ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ))).comp
        Real.tendsto_log_atTop)
  obtain ⟨x₁, hx₁⟩ := (Filter.eventually_atTop.1
    (htend.eventually_gt_atTop (c : ℝ)))
  refine ⟨max x₁ (Real.exp 100), ?_⟩
  intro x hx
  have hx₁x : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxexp : Real.exp 100 ≤ x := le_trans (le_max_right _ _) hx
  have hlog : 100 ≤ Real.log x := by
    calc
      100 = Real.log (Real.exp 100) := by simp
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hxexp
  have hlog1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hcx : (c : ℝ) < Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) := hx₁ x hx₁x
  have hpowhi : 2 * Real.rpow (Real.log x) (1 / 5 : ℝ) <
      (9 / 10 : ℝ) * Real.log x := by
    have hsmall : Real.rpow (Real.log x) (1 / 5 : ℝ) ≤
        Real.rpow (Real.log x) (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
    have hsqrt : Real.sqrt (Real.log x) ≤ Real.log x / 4 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have hlogpos : 0 ≤ Real.log x := by linarith
        nlinarith [sq_nonneg (Real.log x - 16)]
    have hsqrt' : Real.rpow (Real.log x) (1 / 2 : ℝ) ≤ Real.log x / 4 := by
      simpa [Real.sqrt_eq_rpow] using hsqrt
    nlinarith
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 100) hxexp
  have hpowexp : Real.rpow x (9 / 10 : ℝ) =
      Real.exp ((9 / 10 : ℝ) * Real.log x) := by
    calc
      Real.rpow x (9 / 10 : ℝ) =
          Real.exp (Real.log x * (9 / 10 : ℝ)) :=
        Real.rpow_def_of_pos hxpos (9 / 10 : ℝ)
      _ = Real.exp ((9 / 10 : ℝ) * Real.log x) := by congr 1 <;> ring
  have hupper : Real.exp (2 * Real.rpow (Real.log x) (1 / 5 : ℝ)) <
      Real.rpow x (9 / 10 : ℝ) := by
    rw [hpowexp]
    exact Real.exp_lt_exp.mpr hpowhi
  have hp_bounds (p : ℕ) (hp : p ∈ markedPrimes x K a) :
      (c : ℝ) < (p : ℝ) ∧ (p : ℝ) < Real.rpow x (9 / 10 : ℝ) := by
    change p ∈ Finset.univ.biUnion (fun i => primeBand x (a i)) at hp
    rcases Finset.mem_biUnion.mp hp with ⟨i, _, hpi⟩
    dsimp [primeBand] at hpi
    rcases (Finset.mem_filter.mp hpi).2 with ⟨hpprime, hplower, hpupper⟩
    have hai : (1 / 10 : ℝ) < a i ∧ a i < 1 / 5 := ha.2.1 i
    have hpowlo : Real.rpow (Real.log x) (1 / 10 : ℝ) ≤
        Real.rpow (Real.log x) (a i) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 hai.1.le
    have hpowupper : Real.rpow (Real.log x) (a i) ≤
        Real.rpow (Real.log x) (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 hai.2.le
    have hpl : Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) ≤ (p : ℝ) :=
      (Real.exp_le_exp.mpr hpowlo).trans hplower
    have hpu : (p : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) (1 / 5 : ℝ)) :=
      hpupper.trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hpowupper (by norm_num)))
    constructor
    · exact lt_of_lt_of_le hcx hpl
    · exact lt_of_le_of_lt hpu hupper
  constructor
  · intro p hp hdiv
    have hpbound := hp_bounds p hp
    have hple : (p : ℝ) ≤ (c : ℝ) := by
      exact_mod_cast (Nat.le_of_dvd hc hdiv)
    exact (not_lt_of_ge hple) hpbound.1
  · intro Q hQ hQlarge p hp hdiv
    have hpbound := hp_bounds p hp
    have hpPrime : p.Prime := by
      change p ∈ Finset.univ.biUnion (fun i => primeBand x (a i)) at hp
      rcases Finset.mem_biUnion.mp hp with ⟨i, _, hpi⟩
      dsimp [primeBand] at hpi
      exact (Finset.mem_filter.mp hpi).2.1
    have hpEq : p = Q := by
      rcases hQ.eq_one_or_self_of_dvd p hdiv with hpone | hpEq
      · exact False.elim (hpPrime.ne_one hpone)
      · exact hpEq
    have : (p : ℝ) = (Q : ℝ) := by exact_mod_cast hpEq
    rw [this] at hpbound
    linarith

end ArtinPrimitiveRoots.Construction.Proofs.C_BINS
