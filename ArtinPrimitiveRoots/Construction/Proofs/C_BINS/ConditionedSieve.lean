import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.ProgressionSieve
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.ConditionedDensity
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.ConditionedErrors

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Classical
open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Construction.Proofs.C_BINS

noncomputable def conditionedSiftedProgressionPrimeSum
    (x : ℝ) (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (r n : ℕ) (z : ℝ) : ℝ :=
  ∑ Q ∈ Finset.range (⌊2 * x⌋₊ + 1),
    if progressionSieveBaseCondition x M c u r Q ∧
        n ∣ c * r * Q + 1 ∧ roughAbove (c * r * Q + 1) z then
      Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0

/-- The block sieve for a prime bin, with all subset errors reindexed jointly. -/
theorem conditioned_bin_sieve_approx
    (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (r : ℕ) (N : Finset ℕ)
    (x z D Kblock C₀ : ℝ) (H H₀ : ℕ)
    (hK : 0 < Kblock) (hBlock : BlockApproximation Kblock C₀ H₀)
    (hc24 : c = 2 ∨ c = 4) (hΨ : IsTestFunction Ψ)
    (hz : 2 ≤ z) (hD : 0 ≤ D)
    (hN : ∀ n ∈ N, n.Prime ∧ z < (n : ℝ) ∧ Nat.Coprime n (M * r))
    (hBlockSum : ∀ v : ℝ, 1 < v →
      (∑ p ∈ ((primesUpTo z).filter (fun p : ℕ => 2 < p)).filter
          (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2),
        localSieveDensity M r p) ≤ C₀)
    (hcut : ∀ n ∈ N, (n : ℝ) * z ^ (4 * H + 2) ≤ D)
    (hEven : Even H) (hH₀ : H₀ ≤ H) :
    |(∑ n ∈ N, conditionedSiftedProgressionPrimeSum x M c u Ψ r n z) -
        (progressionPrimeSum x M c u Ψ r 1 * progressionSieveProductFor M r z *
          (∑ n ∈ N, 1 / ((n : ℝ) - 1)))| ≤
      Kblock * Real.exp (-(H : ℝ)) *
        (progressionPrimeSum x M c u Ψ r 1 * progressionSieveProductFor M r z *
          (∑ n ∈ N, 1 / ((n : ℝ) - 1))) +
        Kblock * ∑ ℓ ∈ oddSquarefreeUpTo D,
          |progressionPrimeSum x M c u Ψ r ℓ -
            localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1| := by
  classical
  let Qset : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let P : Finset ℕ := (primesUpTo z).filter (fun p : ℕ => 2 < p)
  let wt : ℕ → ℝ := progressionSieveWeight x M c u Ψ r
  let bad : ℕ → ℕ → Prop := fun p Q => p ∣ c * r * Q + 1
  let g : ℕ → ℝ := fun p => localSieveDensity M r p
  let X := progressionPrimeSum x M c u Ψ r 1
  let V := progressionSieveProductFor M r z
  let T : Finset (Finset ℕ) := P.powerset.filter (fun Dset =>
    ((∏ p ∈ Dset, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2))
  let S : ℕ → ℝ := fun n => conditionedSiftedProgressionPrimeSum x M c u Ψ r n z
  let main : ℕ → ℝ := fun n => X / ((n : ℝ) - 1) * V
  let err : ℕ → ℝ := fun ℓ =>
    progressionPrimeSum x M c u Ψ r ℓ - localSieveDensity M r ℓ * X
  have hz0 : 0 ≤ z := (by norm_num : (0 : ℝ) ≤ 2).trans hz
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hP3 : ∀ p ∈ P, 3 ≤ p := by
    intro p hp
    have hpgt : 2 < p := (Finset.mem_filter.mp hp).2
    omega
  have hPle : ∀ p ∈ P, (p : ℝ) ≤ z := by
    intro p hp
    have hpRange := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    exact (Nat.le_floor_iff hz0).mp
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hpRange))
  have hN3 (n : ℕ) (hn : n ∈ N) : 3 ≤ n := by
    have hnR : (2 : ℝ) < n := hz.trans_lt (hN n hn).2.1
    have hnNat : 2 < n := by exact_mod_cast hnR
    omega
  have hnotP (n : ℕ) (hn : n ∈ N) : n ∉ P := by
    intro hnP
    exact not_lt_of_ge (hPle n hnP) (hN n hn).2.1
  have hDisjoint : Disjoint P N :=
    Finset.disjoint_left.mpr (fun n hnP hnN => hnotP n hnN hnP)
  have hTsubset : ∀ Dset ∈ T, Dset ⊆ P := by
    intro Dset hDset
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hDset).1
  have hPrimeD (Dset : Finset ℕ) (hDset : Dset ∈ T) :
      ∀ p ∈ Dset, p.Prime ∧ 3 ≤ p := by
    intro p hp
    exact ⟨hPprime p (hTsubset Dset hDset hp), hP3 p (hTsubset Dset hDset hp)⟩
  have hnotD (n : ℕ) (hn : n ∈ N) (Dset : Finset ℕ) (hDset : Dset ∈ T) :
      n ∉ Dset := fun hnD => hnotP n hn (hTsubset Dset hDset hnD)
  have hPrimeInsert (n : ℕ) (hn : n ∈ N) (Dset : Finset ℕ) (hDset : Dset ∈ T) :
      ∀ p ∈ insert n Dset, p.Prime ∧ 3 ≤ p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with hpn | hp
    · subst p
      exact ⟨(hN n hn).1, hN3 n hn⟩
    · exact hPrimeD Dset hDset p hp
  have hImage (n : ℕ) (hn : n ∈ N) (Dset : Finset ℕ) (hDset : Dset ∈ T) :
      n * (∏ p ∈ Dset, p) ∈ oddSquarefreeUpTo D := by
    obtain ⟨hOdd, hSq⟩ :=
      primeProduct_odd_squarefree (insert n Dset) (hPrimeInsert n hn Dset hDset)
    rw [Finset.prod_insert (hnotD n hn Dset hDset)] at hOdd hSq
    have hprodReal : ((n * (∏ p ∈ Dset, p) : ℕ) : ℝ) ≤ D := by
      calc
        _ = (n : ℝ) * ((∏ p ∈ Dset, p : ℕ) : ℝ) := Nat.cast_mul _ _
        _ ≤ (n : ℝ) * z ^ (4 * H + 2) :=
          mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hDset).2 (Nat.cast_nonneg n)
        _ ≤ D := hcut n hn
    have hprodNat : n * (∏ p ∈ Dset, p) ≤ ⌊D⌋₊ :=
      (Nat.le_floor_iff hD).mpr hprodReal
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hprodNat), hOdd, hSq⟩
  have hwt : ∀ Q ∈ Qset, 0 ≤ wt Q := by
    intro Q hQ
    by_cases hbase : progressionSieveBaseCondition x M c u r Q
    · simp [wt, progressionSieveWeight, hbase, hΨ.2.2.1]
    · simp [wt, progressionSieveWeight, hbase]
  have hXnonneg : 0 ≤ X := by
    have hXsum : (∑ Q ∈ Qset, wt Q) = X :=
      progressionSieveWeight_sum_eq x M c u Ψ r
    rw [← hXsum]
    exact Finset.sum_nonneg hwt
  have hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 := by
    intro p hp
    have h := localSieveDensity_prime_bounds M r p (hPprime p hp) (hP3 p hp)
    exact ⟨h.1, h.2.1⟩
  have hBlockSumP : ∀ v : ℝ, 1 < v →
      ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀ :=
    hBlockSum
  have hVeq : (∏ p ∈ P, (1 - g p)) = V := rfl
  have hcEven : Even c := by
    rcases hc24 with h | h <;> rw [h] <;> norm_num [Even]
  have hOdd (Q : ℕ) : Odd (c * r * Q + 1) := by
    rcases hcEven with ⟨k, hk⟩
    refine ⟨k * r * Q, ?_⟩
    rw [hk]
    ring
  have hAvoid (Q : ℕ) :
      (∀ p ∈ P, ¬ bad p Q) ↔ roughAbove (c * r * Q + 1) z :=
    avoidsOddPrimes_iff_roughAbove (c * r * Q + 1) z hz0 (hOdd Q)
  have hProgression (ℓ : ℕ) : progressionPrimeSum x M c u Ψ r ℓ =
      ∑ Q ∈ Qset, if progressionSieveBaseCondition x M c u r Q ∧
          ℓ ∣ c * r * Q + 1 then Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0 := by
    simp only [Qset, progressionPrimeSum, Finset.sum_filter,
      progressionSieveBaseCondition, and_assoc]
  have hPer (n : ℕ) (hn : n ∈ N) :
      |S n - main n| ≤ Kblock * Real.exp (-(H : ℝ)) * main n +
        Kblock * ∑ Dset ∈ T, |err (n * (∏ p ∈ Dset, p))| := by
    let A := Qset.filter (fun Q : ℕ => n ∣ c * r * Q + 1)
    let Xn := X / ((n : ℝ) - 1)
    let blockError : Finset ℕ → ℝ := fun Dset =>
      (∑ Q ∈ A with ∀ p ∈ Dset, bad p Q, wt Q) - Xn * ∏ p ∈ Dset, g p
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hN3 n hn
    have hXn : 0 ≤ Xn := div_nonneg hXnonneg (by linarith only [hnR])
    have hApplied :=
      hBlock ℕ A wt (fun Q hQ => hwt Q (Finset.mem_filter.mp hQ).1)
        z hz P (fun p hp => ⟨hPprime p hp, hPle p hp⟩)
        bad Xn g hXn hg hBlockSumP H hEven hH₀
    have hSurvivor : (∑ Q ∈ A with ∀ p ∈ P, ¬ bad p Q, wt Q) = S n := by
      dsimp [A, S, conditionedSiftedProgressionPrimeSum]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro Q hQ
      simp only [hAvoid Q]
      by_cases hDiv : n ∣ c * r * Q + 1 <;>
        by_cases hBase : progressionSieveBaseCondition x M c u r Q <;>
        by_cases hRough : roughAbove (c * r * Q + 1) z <;>
        simp [wt, progressionSieveWeight, hDiv, hBase, hRough]
    have hEid (Dset : Finset ℕ) (hDset : Dset ∈ T) :
        blockError Dset = err (n * (∏ p ∈ Dset, p)) := by
      have hDiviff (Q : ℕ) :
          (n ∣ c * r * Q + 1 ∧ ∀ p ∈ Dset, bad p Q) ↔
            n * (∏ p ∈ Dset, p) ∣ c * r * Q + 1 := by
        have h := (primeSubset_product_dvd_iff (insert n Dset) (insert n Dset)
          (fun p hp => (hPrimeInsert n hn Dset hDset p hp).1)
          (fun _ hp => hp) (c * r * Q + 1)).symm
        rw [Finset.prod_insert (hnotD n hn Dset hDset)] at h
        simpa only [Finset.forall_mem_insert, bad] using h
      have hSumD : (∑ Q ∈ A with ∀ p ∈ Dset, bad p Q, wt Q) =
          progressionPrimeSum x M c u Ψ r (n * (∏ p ∈ Dset, p)) := by
        rw [hProgression]
        simp only [A, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro Q hQ
        by_cases hDiv : n ∣ c * r * Q + 1
        · by_cases hAll : ∀ p ∈ Dset, bad p Q
          · have hProd := (hDiviff Q).mp ⟨hDiv, hAll⟩
            rw [if_pos hDiv, if_pos hAll]
            simp only [wt, progressionSieveWeight, hProd, and_true]
          · have hNotProd : ¬ n * (∏ p ∈ Dset, p) ∣ c * r * Q + 1 :=
              fun h => hAll ((hDiviff Q).mpr h).2
            simp [hDiv, hAll, hNotProd]
        · have hNotProd : ¬ n * (∏ p ∈ Dset, p) ∣ c * r * Q + 1 :=
            fun h => hDiv ((hDiviff Q).mpr h).1
          simp [hDiv, hNotProd]
      dsimp [blockError, err, Xn, g]
      rw [hSumD, localSieveDensity_product_of_primes M r Dset (hPrimeD Dset hDset),
        conditioned_density_product M r n Dset (hN n hn).1 (hN3 n hn)
          (hN n hn).2.2 (hnotD n hn Dset hDset) (hPrimeD Dset hDset)]
      ring
    have hErrorSum : (∑ Dset ∈ T, |blockError Dset|) =
        ∑ Dset ∈ T, |err (n * (∏ p ∈ Dset, p))| := by
      apply Finset.sum_congr rfl
      intro Dset hDset
      rw [hEid Dset hDset]
    have hRaw :
        |(∑ Q ∈ A with ∀ p ∈ P, ¬ bad p Q, wt Q) - Xn * (∏ p ∈ P, (1 - g p))| ≤
          Kblock * Real.exp (-(H : ℝ)) * (Xn * (∏ p ∈ P, (1 - g p))) +
            Kblock * ∑ Dset ∈ T, |blockError Dset| := by
      simpa [T, blockError, A, Qset, wt, bad, g, Xn, Finset.sum_filter] using hApplied
    rw [hSurvivor, hVeq, hErrorSum] at hRaw
    simpa only [main, Xn] using hRaw
  have hErrDom : (∑ n ∈ N, ∑ Dset ∈ T, |err (n * (∏ p ∈ Dset, p))|) ≤
      ∑ ℓ ∈ oddSquarefreeUpTo D, |err ℓ| :=
    conditioned_moduli_absError_sum_le D P N T hPprime
      (fun n hn => (hN n hn).1) hDisjoint hTsubset hImage err
  have hMainSum : (∑ n ∈ N, main n) =
      X * V * (∑ n ∈ N, 1 / ((n : ℝ) - 1)) := by
    simp only [main, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hTotal : |(∑ n ∈ N, S n) - ∑ n ∈ N, main n| ≤
      Kblock * Real.exp (-(H : ℝ)) * (∑ n ∈ N, main n) +
        Kblock * (∑ n ∈ N, ∑ Dset ∈ T, |err (n * (∏ p ∈ Dset, p))|) := by
    calc
      _ = |∑ n ∈ N, (S n - main n)| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ n ∈ N, |S n - main n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ N,
          (Kblock * Real.exp (-(H : ℝ)) * main n +
            Kblock * ∑ Dset ∈ T, |err (n * (∏ p ∈ Dset, p))|) :=
        Finset.sum_le_sum hPer
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hFinal : |(∑ n ∈ N, S n) - ∑ n ∈ N, main n| ≤
      Kblock * Real.exp (-(H : ℝ)) * (∑ n ∈ N, main n) +
        Kblock * ∑ ℓ ∈ oddSquarefreeUpTo D, |err ℓ| :=
    hTotal.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hErrDom hK.le))
  rw [hMainSum] at hFinal
  simpa only [S, X, V, err] using hFinal

end ArtinPrimitiveRoots.Proofs.c_bins_sol
