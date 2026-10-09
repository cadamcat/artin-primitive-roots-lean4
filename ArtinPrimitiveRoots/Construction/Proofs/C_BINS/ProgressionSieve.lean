import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.BlockBounds
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.Positivity
import ArtinPrimitiveRoots.Sieve.Block

namespace ArtinPrimitiveRoots.Construction.Proofs.C_BINS

open Classical
open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.TypeII

noncomputable def progressionSieveBaseCondition
    (x : ℝ) (M c : ℕ) (u : ℤ) (r Q : ℕ) : Prop :=
  Q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
    (((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])

noncomputable def progressionSieveWeight
    (x : ℝ) (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (r Q : ℕ) : ℝ :=
  if progressionSieveBaseCondition x M c u r Q then
    Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0

noncomputable def siftedProgressionPrimeSum
    (x : ℝ) (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (r : ℕ) (z : ℝ) : ℝ :=
  ∑ Q ∈ Finset.range (⌊2 * x⌋₊ + 1),
    if progressionSieveBaseCondition x M c u r Q ∧
        roughAbove (c * r * Q + 1) z then
      Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0

/-- The first, absolute-error half of `lem_block`, with its finite sums exposed. -/
def BlockApproximation (K C₀ : ℝ) (H₀ : ℕ) : Prop :=
  ∀ (α : Type) (A : Finset α) (wt : α → ℝ), (∀ a ∈ A, 0 ≤ wt a) →
    ∀ (z : ℝ), 2 ≤ z → ∀ (P : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) →
      ∀ (bad : ℕ → α → Prop) (X' : ℝ) (g : ℕ → ℝ), 0 ≤ X' →
        (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2) →
        (∀ v : ℝ, 1 < v →
          ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀) →
        let S : ℝ := ∑ a ∈ A with ∀ p ∈ P, ¬ bad p a, wt a
        let main : ℝ := X' * ∏ p ∈ P, (1 - g p)
        let E : Finset ℕ → ℝ := fun D =>
          (∑ a ∈ A with ∀ p ∈ D, bad p a, wt a) - X' * ∏ p ∈ D, g p
        ∀ H : ℕ, Even H → H₀ ≤ H →
          |S - main| ≤ K * Real.exp (-(H : ℝ)) * main +
            K * ∑ D ∈ P.powerset with
              ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2), |E D|

theorem exists_blockApproximation (C₀ : ℝ) :
    ∃ K : ℝ, ∃ H₀ : ℕ, 0 < K ∧ BlockApproximation K C₀ H₀ := by
  obtain ⟨K, hK, H₀, hBlock⟩ :=
    ArtinPrimitiveRoots.Sieve.lem_block (1 / 2 : ℝ) C₀ (by norm_num)
  refine ⟨K, H₀, hK, fun α A wt hwt z hz P hP bad X' g hX hg hBlockSum => ?_⟩
  have hg' : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 - (1 / 2 : ℝ) := by
    intro p hp
    rcases hg p hp with ⟨hlo, hhi⟩
    refine ⟨hlo, ?_⟩
    have hEq : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [hEq]
    exact hhi
  exact (hBlock α A wt hwt z hz P hP bad X' g hX hg' hBlockSum).1

private theorem primesUpTo_mem_of_nonneg {z : ℝ} (hz : 0 ≤ z) {p : ℕ} :
    p ∈ primesUpTo z ↔ p.Prime ∧ (p : ℝ) ≤ z := by
  unfold primesUpTo
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff hz]
  exact and_comm

theorem progressionSieveProduct_nonneg (M : ℕ) (y : ℝ) :
    0 ≤ progressionSieveProduct M y := by
  classical
  unfold progressionSieveProduct
  apply Finset.prod_nonneg
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpBase, hpCond⟩
  rcases Finset.mem_filter.mp hpBase with ⟨_, hpPrime⟩
  have hp3 : 3 ≤ p := by omega
  have hpCast3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hden : 0 < (p : ℝ) - 1 := by linarith
  have hdenle : 1 ≤ (p : ℝ) - 1 := by linarith
  have hfrac : 1 / ((p : ℝ) - 1) ≤ 1 := (div_le_one₀ hden).2 hdenle
  exact sub_nonneg.mpr hfrac

theorem avoidsOddPrimes_iff_roughAbove
    (d : ℕ) (z : ℝ) (hz : 0 ≤ z) (hdOdd : Odd d) :
    (∀ p ∈ (primesUpTo z).filter (fun p : ℕ => 2 < p), ¬ p ∣ d) ↔
      roughAbove d z := by
  rw [roughAbove_iff_avoids_primesUpTo d z hz]
  constructor
  · intro h p hp
    by_cases hp2 : p = 2
    · subst p
      intro hdiv
      rcases hdOdd with ⟨k, hk⟩
      have htwo : 2 ∣ 2 * k + 1 := by simpa [hk] using hdiv
      omega
    · have hpPrime := (primesUpTo_mem_of_nonneg hz).mp hp |>.1
      have hpLe : 2 ≤ p := hpPrime.two_le
      have hpgt : 2 < p := by omega
      exact h p (Finset.mem_filter.mpr ⟨hp, hpgt⟩)
  · intro h p hp
    exact h p (Finset.mem_filter.mp hp).1

theorem progressionSieveWeight_sum_eq
    (x : ℝ) (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (r : ℕ) :
    (∑ Q ∈ Finset.range (⌊2 * x⌋₊ + 1),
      progressionSieveWeight x M c u Ψ r Q) =
      progressionPrimeSum x M c u Ψ r 1 := by
  classical
  simp [progressionPrimeSum, progressionSieveWeight,
    progressionSieveBaseCondition, Finset.sum_filter, and_assoc]

theorem siftedProgressionPrimeSum_eq_avoids
    (x : ℝ) (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (r : ℕ) (z : ℝ)
    (hc24 : c = 2 ∨ c = 4) (hz : 0 ≤ z) :
    (∑ Q ∈ Finset.range (⌊2 * x⌋₊ + 1) with
        ∀ p ∈ (primesUpTo z).filter (fun p : ℕ => 2 < p),
          ¬ p ∣ c * r * Q + 1,
      progressionSieveWeight x M c u Ψ r Q) =
      siftedProgressionPrimeSum x M c u Ψ r z := by
  classical
  rw [Finset.sum_filter]
  unfold siftedProgressionPrimeSum
  apply Finset.sum_congr rfl
  intro Q hQ
  have hcEven : Even c := by
    rcases hc24 with h | h <;> rw [h] <;> norm_num [Even]
  have hProdEven : Even (c * r * Q) := by
    rcases hcEven with ⟨k, hk⟩
    refine ⟨k * r * Q, ?_⟩
    rw [hk]
    ring
  have hOdd : Odd (c * r * Q + 1) := by
    rcases hProdEven with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    ring
  have hAvoid := avoidsOddPrimes_iff_roughAbove (c * r * Q + 1) z hz hOdd
  have hAvoid' :
      (∀ p ∈ primesUpTo z, 2 < p → ¬ p ∣ c * r * Q + 1) ↔
        roughAbove (c * r * Q + 1) z := by
    constructor
    · intro h
      apply hAvoid.mp
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpUp, hpgt⟩
      exact h p hpUp hpgt
    · intro h p hp hpgt
      exact (hAvoid.mpr h) p (Finset.mem_filter.mpr ⟨hp, hpgt⟩)
  by_cases hbase : progressionSieveBaseCondition x M c u r Q
  · by_cases hrough : roughAbove (c * r * Q + 1) z <;>
      simp [progressionSieveWeight, progressionSieveBaseCondition,
        hAvoid', hbase, hrough]
  · have hnotBR : ¬ (progressionSieveBaseCondition x M c u r Q ∧
        roughAbove (c * r * Q + 1) z) := fun h => hbase h.1
    simp [progressionSieveWeight, hbase, hnotBR]

theorem siftedProgressionPrimeSum_lower
    (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (r : ℕ)
    (x z D K C₀ : ℝ) (H H₀ : ℕ)
    (hK : 0 < K) (hBlock : BlockApproximation K C₀ H₀)
    (hBlockSum : ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ v : ℝ, 1 < v → ∀ r M : ℕ, (∀ p ∈ P, 3 ≤ p) →
        (∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2),
          localSieveDensity M r p) ≤ C₀)
    (hc24 : c = 2 ∨ c = 4) (hΨ : IsTestFunction Ψ)
    (hz : 2 ≤ z) (hD : 0 ≤ D)
    (hcut : z ^ (4 * H + 2) ≤ D) (hEven : Even H) (hH₀ : H₀ ≤ H) :
    siftedProgressionPrimeSum x M c u Ψ r z ≥
      progressionPrimeSum x M c u Ψ r 1 * progressionSieveProductFor M r z -
        K * Real.exp (-(H : ℝ)) *
          (progressionPrimeSum x M c u Ψ r 1 * progressionSieveProductFor M r z) -
        K * ∑ ℓ ∈ oddSquarefreeUpTo D,
          |progressionPrimeSum x M c u Ψ r ℓ -
            localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1| := by
  classical
  let Qset : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let P : Finset ℕ := (primesUpTo z).filter (fun p : ℕ => 2 < p)
  let wt : ℕ → ℝ := progressionSieveWeight x M c u Ψ r
  let bad : ℕ → ℕ → Prop := fun p Q => p ∣ c * r * Q + 1
  let g : ℕ → ℝ := fun p => localSieveDensity M r p
  let X : ℝ := progressionPrimeSum x M c u Ψ r 1
  let survivorSum : ℝ := ∑ Q ∈ Qset with ∀ p ∈ P, ¬ bad p Q, wt Q
  let main : ℝ := X * ∏ p ∈ P, (1 - g p)
  let T : Finset (Finset ℕ) := P.powerset.filter (fun Dset =>
    ((∏ p ∈ Dset, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2))
  let blockError : Finset ℕ → ℝ := fun Dset =>
    (∑ Q ∈ Qset with ∀ p ∈ Dset, bad p Q, wt Q) -
      X * ∏ p ∈ Dset, g p
  let err : ℕ → ℝ := fun ℓ =>
    progressionPrimeSum x M c u Ψ r ℓ - localSieveDensity M r ℓ * X
  have hZnonneg : 0 ≤ z := le_trans (by norm_num) hz
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact ((primesUpTo_mem_of_nonneg hZnonneg).mp
      (Finset.mem_filter.mp hp).1).1
  have hP3 : ∀ p ∈ P, 3 ≤ p := by
    intro p hp
    have hpgt : 2 < p := (Finset.mem_filter.mp hp).2
    omega
  have hPle : ∀ p ∈ P, (p : ℝ) ≤ z := by
    intro p hp
    exact ((primesUpTo_mem_of_nonneg hZnonneg).mp
      (Finset.mem_filter.mp hp).1).2
  have hwt : ∀ Q ∈ Qset, 0 ≤ wt Q := by
    intro Q hQ
    by_cases hbase : progressionSieveBaseCondition x M c u r Q
    · simp [wt, progressionSieveWeight, hbase, hΨ.2.2.1]
    · simp [wt, progressionSieveWeight, hbase]
  have hXsum : (∑ Q ∈ Qset, wt Q) = X := by
    dsimp [Qset, wt, X]
    rw [progressionSieveWeight_sum_eq]
  have hXnonneg : 0 ≤ X := by
    rw [← hXsum]
    apply Finset.sum_nonneg
    intro Q hQ
    exact hwt Q hQ
  have hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 := by
    intro p hp
    have hpprime := hPprime p hp
    have hp3 := hP3 p hp
    have hbound := localSieveDensity_prime_bounds M r p hpprime hp3
    exact ⟨by simpa [g] using hbound.1, by simpa [g] using hbound.2.1⟩
  have hBlockSumP : ∀ v : ℝ, 1 < v →
      ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀ := by
    intro v hv
    simpa [g] using hBlockSum P hPprime v hv r M hP3
  have hApplied :=
    hBlock ℕ Qset wt hwt z hz P (by
      intro p hp
      exact ⟨hPprime p hp, hPle p hp⟩) bad X g hXnonneg hg hBlockSumP
      H hEven hH₀
  have hTsubset : ∀ Dset ∈ T, Dset ⊆ P := by
    intro Dset hDset
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hDset).1
  have hPrimeOdd (Dset : Finset ℕ) (hDset : Dset ∈ T) :
      ∀ p ∈ Dset, p.Prime ∧ 3 ≤ p := by
    intro p hp
    exact ⟨hPprime p (hTsubset Dset hDset hp), hP3 p (hTsubset Dset hDset hp)⟩
  have hImage (Dset : Finset ℕ) (hDset : Dset ∈ T) :
      (∏ p ∈ Dset, p) ∈ oddSquarefreeUpTo D := by
    obtain ⟨hOdd, hSq⟩ := primeProduct_odd_squarefree Dset (hPrimeOdd Dset hDset)
    have hprodReal : ((∏ p ∈ Dset, p : ℕ) : ℝ) ≤ D := by
      exact (Finset.mem_filter.mp hDset).2.trans hcut
    have hprodNat : (∏ p ∈ Dset, p) ≤ ⌊D⌋₊ :=
      (Nat.le_floor_iff hD).2 hprodReal
    dsimp [oddSquarefreeUpTo]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hprodNat), hOdd, hSq⟩
  have hEid (Dset : Finset ℕ) (hDset : Dset ∈ T) :
      blockError Dset = err (∏ p ∈ Dset, p) := by
    have hDsub : Dset ⊆ P := hTsubset Dset hDset
    have hDiviff (Q : ℕ) :
        (∀ p ∈ Dset, bad p Q) ↔ (∏ p ∈ Dset, p) ∣ c * r * Q + 1 := by
      simpa [bad] using
        (primeSubset_product_dvd_iff P Dset hPprime hDsub (c * r * Q + 1)).symm
    have hSumD :
      (∑ Q ∈ Qset with ∀ p ∈ Dset, bad p Q, wt Q) =
          progressionPrimeSum x M c u Ψ r (∏ p ∈ Dset, p) := by
      calc
        _ = ∑ Q ∈ Qset, if ∀ p ∈ Dset, bad p Q then wt Q else 0 :=
          by rw [Finset.sum_filter]
        _ = progressionPrimeSum x M c u Ψ r (∏ p ∈ Dset, p) := by
          dsimp [Qset, wt, progressionSieveWeight, X]
          unfold progressionPrimeSum
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro Q hQ
          by_cases hdiv : (∏ p ∈ Dset, p) ∣ c * r * Q + 1
          · have hDcond := (hDiviff Q).2 hdiv
            rw [if_pos hDcond]
            by_cases hbase : progressionSieveBaseCondition x M c u r Q
            · simp [progressionSieveBaseCondition, progressionSieveWeight,
                hbase, hdiv]
            · simp [progressionSieveBaseCondition, progressionSieveWeight,
                hbase, hdiv]
          · have hDcond : ¬ ∀ p ∈ Dset, bad p Q := fun h =>
              hdiv ((hDiviff Q).1 h)
            rw [if_neg hDcond]
            simp [progressionSieveBaseCondition, hdiv]
    have hDensity := localSieveDensity_product_of_primes M r Dset (hPrimeOdd Dset hDset)
    dsimp [blockError, err, g, X]
    rw [hSumD, hDensity]
    ring
  have hErrDom :
      (∑ Dset ∈ T, |blockError Dset|) ≤
        ∑ ℓ ∈ oddSquarefreeUpTo D, |err ℓ| := by
    calc
      _ = ∑ Dset ∈ T, |err (∏ p ∈ Dset, p)| := by
        apply Finset.sum_congr rfl
        intro Dset hDset
        rw [hEid Dset hDset]
      _ ≤ ∑ ℓ ∈ oddSquarefreeUpTo D, |err ℓ| :=
        primeSubset_absError_sum_le D P T hPprime hTsubset hImage err
  have hApplied' : |survivorSum - main| ≤
      K * Real.exp (-(H : ℝ)) * main + K * ∑ Dset ∈ T, |blockError Dset| := by
    simpa [BlockApproximation, survivorSum, main, T, blockError,
      Qset, wt, bad, g] using hApplied
  have hApprox : |survivorSum - main| ≤
      K * Real.exp (-(H : ℝ)) * main + K * ∑ ℓ ∈ oddSquarefreeUpTo D, |err ℓ| := by
    have hErrMul := mul_le_mul_of_nonneg_left hErrDom hK.le
    nlinarith [hApplied']
  have hSurvivorEq : survivorSum = siftedProgressionPrimeSum x M c u Ψ r z := by
    simpa [survivorSum, Qset, wt, P, bad] using
      (siftedProgressionPrimeSum_eq_avoids x M c u Ψ r z hc24 hZnonneg)
  have hMainEq : main =
      progressionPrimeSum x M c u Ψ r 1 * progressionSieveProductFor M r z := by
    simp [main, X, P, g, progressionSieveProductFor]
  have hLower :
      main - (K * Real.exp (-(H : ℝ)) * main +
        K * ∑ ℓ ∈ oddSquarefreeUpTo D, |err ℓ|) ≤ survivorSum := by
    have hNeg := neg_abs_le (survivorSum - main)
    linarith [hApprox, hNeg]
  rw [hSurvivorEq, hMainEq] at hLower
  dsimp [err, X] at hLower
  nlinarith [hLower]

end ArtinPrimitiveRoots.Construction.Proofs.C_BINS
