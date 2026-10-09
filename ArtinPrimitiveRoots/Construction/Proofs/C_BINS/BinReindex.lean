import ArtinPrimitiveRoots.Construction.Proofs.C_BV.Mass
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.ConditionedSieve

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Classical
open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.Construction.Proofs.C_BINS
open ArtinPrimitiveRoots.TypeII

/-- Apply finite mass reindexing to a test function masked by natural prime divisibility. -/
theorem prime_divisor_bin_group_reindex
    (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ)
    (Ψ : ℝ → ℝ) (γ γ' : ℝ)
    (hc24 : c = 2 ∨ c = 4) (hx2 : 2 ≤ x)
    (hL : (4 : ℝ) ^ 10 ≤ Real.log x)
    (ha : ValidBands K a) (hΨsupp : Function.support Ψ ⊆ Set.Ioo 1 2)
    (hSupport : ∀ d, conWeight x M c u K a Ψ d ≠ 0 →
      x < (d : ℝ) ∧ (d : ℝ) < 2 * x ∧
        ∃ r Q : ℕ, d - 1 = c * r * Q ∧ Q.Prime ∧
          Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
          IsGroupInteger x K a r ∧
          (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) ∧
          markedWeight x K a (1 / 2 : ℝ) (d - 1) =
            markedWeight x K a (1 / 2 : ℝ) r) :
    primeDivisorBinSum x M c u K a Ψ γ γ' =
      ∑ r ∈ (Finset.range (⌊2 * x⌋₊ + 1)).filter
          (fun r => IsGroupInteger x K a r),
        markedWeight x K a (1 / 2 : ℝ) r *
          (∑ n ∈ (primesUpTo (Real.rpow x γ')).filter
              (fun n : ℕ => Real.rpow x γ < (n : ℝ)),
            conditionedSiftedProgressionPrimeSum x M c u Ψ r n (roughCutoff x)) := by
  classical
  have hxpos : 0 < x := by linarith
  let W : ℝ := roughCutoff x
  let R : Finset ℕ := (Finset.range (⌊2 * x⌋₊ + 1)).filter
    (fun r => IsGroupInteger x K a r)
  let N : Finset ℕ := (primesUpTo (Real.rpow x γ')).filter
    (fun n : ℕ => Real.rpow x γ < (n : ℝ))
  let test : ℕ → ℝ → ℝ := fun n y =>
    if n ∣ ⌊x * y⌋₊ ∧ roughAbove ⌊x * y⌋₊ W then Ψ y else 0
  have hFloor (d : ℕ) : ⌊x * ((d : ℝ) / x)⌋₊ = d := by
    have hmul : x * ((d : ℝ) / x) = (d : ℝ) := by
      field_simp [ne_of_gt hxpos] <;> ring
    rw [hmul]
    simp
  have hSample (n d : ℕ) : test n ((d : ℝ) / x) =
      if n ∣ d ∧ roughAbove d W then Ψ ((d : ℝ) / x) else 0 := by
    dsimp [test]
    rw [hFloor]
  have hWeight (n d : ℕ) : conWeight x M c u K a (test n) d =
      if n ∣ d ∧ roughAbove d W then conWeight x M c u K a Ψ d else 0 := by
    unfold conWeight
    rw [hSample]
    by_cases hmask : n ∣ d ∧ roughAbove d W <;>
      by_cases hcond : 1 < d ∧ (d : ℤ) ≡ u [ZMOD M] <;>
        simp [hmask, hcond]
  have hOriginalNZ (n d : ℕ) (hd : conWeight x M c u K a (test n) d ≠ 0) :
      conWeight x M c u K a Ψ d ≠ 0 := by
    intro hzero
    apply hd
    rw [hWeight n d, hzero] <;> simp
  have hTestSupport (n : ℕ) : Function.support (test n) ⊆ Set.Ioo 1 2 := by
    intro y hy
    apply hΨsupp
    change Ψ y ≠ 0
    intro hzero
    have hmasked : test n y ≠ 0 := hy
    apply hmasked
    simp only [test, hzero, ite_self]
  have hProgression (n r : ℕ) :
      progressionPrimeSum x M c u (test n) r 1 =
        conditionedSiftedProgressionPrimeSum x M c u Ψ r n W := by
    unfold progressionPrimeSum conditionedSiftedProgressionPrimeSum
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Q hQ
    simp only [one_dvd, and_true]
    rw [hSample n (c * r * Q + 1)]
    by_cases hbase : progressionSieveBaseCondition x M c u r Q <;>
      by_cases hmask : n ∣ c * r * Q + 1 ∧ roughAbove (c * r * Q + 1) W <;>
        simp only [progressionSieveBaseCondition] at hbase <;>
          simp [hbase, hmask, progressionSieveBaseCondition]
  have hMass (n : ℕ) :
      (∑ d ∈ Finset.range (⌊2 * x⌋₊ + 1),
        if n ∣ d ∧ roughAbove d W then conWeight x M c u K a Ψ d else 0) =
      ∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r *
        conditionedSiftedProgressionPrimeSum x M c u Ψ r n W := by
    have hRaw := ArtinPrimitiveRoots.Proofs.C_BV.conTotalMass_eq_groupProgressionSum
      x M c u K a (test n) hc24 hx2 hxpos hL ha (hTestSupport n)
        (fun d hd => hSupport d (hOriginalNZ n d hd))
    simpa only [conTotalMass, hWeight n, hProgression n, R] using hRaw
  change (∑ n ∈ N, ∑ d ∈ Finset.range (⌊2 * x⌋₊ + 1),
      if n ∣ d ∧ roughAbove d W then conWeight x M c u K a Ψ d else 0) =
    ∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r *
      (∑ n ∈ N, conditionedSiftedProgressionPrimeSum x M c u Ψ r n W)
  calc
    _ = ∑ n ∈ N, ∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r *
        conditionedSiftedProgressionPrimeSum x M c u Ψ r n W := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hMass n
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]

end ArtinPrimitiveRoots.Proofs.c_bins_sol
