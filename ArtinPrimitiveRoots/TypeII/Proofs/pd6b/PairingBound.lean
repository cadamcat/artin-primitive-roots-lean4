import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

/-- Removing two projections costs the absolute sum over edges with a bad endpoint. -/
theorem maskedPairing_difference_le {ι : Type*} [Fintype ι]
    (f g : ι → ℂ) (k : ι → ι → ℂ) (good : ι → Prop)
    (μ B : ℝ) (hμ : 0 ≤ μ) (hB : 0 ≤ B)
    (hf : ∀ i, ‖f i‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B) :
    ‖(μ : ℂ) * (∑ i, (f i * if good i then (1 : ℂ) else 0) *
        ∑ j, k i j * (if good j then g j else 0)) -
      (μ : ℂ) * (∑ i, f i * ∑ j, k i j * g j)‖ ≤
      μ * B ^ 2 * ∑ i, ∑ j, if ¬ good i ∨ ¬ good j then ‖k i j‖ else 0 := by
  classical
  let T (i j : ι) :=
    (f i * if good i then (1 : ℂ) else 0) *
      (k i j * (if good j then g j else 0)) - f i * (k i j * g j)
  have hdiff :
      (∑ i, (f i * if good i then (1 : ℂ) else 0) *
          ∑ j, k i j * (if good j then g j else 0)) -
        (∑ i, f i * ∑ j, k i j * g j) = ∑ i, ∑ j, T i j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm (i j : ι) :
      ‖T i j‖ ≤ B ^ 2 * (if ¬ good i ∨ ¬ good j then ‖k i j‖ else 0) := by
    have hnorm : ‖f i‖ * (‖k i j‖ * ‖g j‖) ≤ B ^ 2 * ‖k i j‖ := by
      calc
        _ ≤ B * (‖k i j‖ * B) :=
          mul_le_mul (hf i)
            (mul_le_mul_of_nonneg_left (hg j) (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hB
        _ = _ := by ring
    by_cases hi : good i <;> by_cases hj : good j
    · simp [T, hi, hj]
    · simpa [T, hi, hj, norm_mul] using hnorm
    · simpa [T, hi, hj, norm_mul] using hnorm
    · simpa [T, hi, hj, norm_mul] using hnorm
  rw [← mul_sub, hdiff, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ]
  calc
    μ * ‖∑ i, ∑ j, T i j‖ ≤ μ * (∑ i, ∑ j, ‖T i j‖) := by
      apply mul_le_mul_of_nonneg_left _ hμ
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ ≤ μ * (B ^ 2 * (∑ i, ∑ j, if ¬ good i ∨ ¬ good j then ‖k i j‖ else 0)) := by
      apply mul_le_mul_of_nonneg_left _ hμ
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j hj => hterm i j)
    _ = _ := by ring

/-- A symmetric envelope reduces failure at either endpoint to twice the source-bad sum. -/
theorem maskedPairing_difference_le_sourceEnvelope {ι : Type*} [Fintype ι]
    (f g : ι → ℂ) (k : ι → ι → ℂ) (good : ι → Prop) (w : ι → ι → ℝ)
    (μ B : ℝ) (hμ : 0 ≤ μ) (hB : 0 ≤ B)
    (hf : ∀ i, ‖f i‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B)
    (hkernel : ∀ i j, ‖k i j‖ ≤ w i j) (hsymm : ∀ i j, w i j = w j i) :
    ‖(μ : ℂ) * (∑ i, (f i * if good i then (1 : ℂ) else 0) *
        ∑ j, k i j * (if good j then g j else 0)) -
      (μ : ℂ) * (∑ i, f i * ∑ j, k i j * g j)‖ ≤
      2 * μ * B ^ 2 * ∑ i, ∑ j, if ¬ good i then w i j else 0 := by
  classical
  have hw (i j : ι) : 0 ≤ w i j := (norm_nonneg _).trans (hkernel i j)
  have hterm (i j : ι) : (if ¬ good i ∨ ¬ good j then ‖k i j‖ else 0) ≤
      (if ¬ good i then w i j else 0) + (if ¬ good j then w i j else 0) := by
    by_cases hi : good i <;> by_cases hj : good j
    · simp [hi, hj]
    · simpa [hi, hj] using hkernel i j
    · simpa [hi, hj] using hkernel i j
    · simp only [hi, hj, not_false_eq_true, true_or, if_true]
      exact (hkernel i j).trans (le_add_of_nonneg_right (hw i j))
  have hswap : (∑ i : ι, ∑ j : ι, if ¬ good j then w i j else 0) =
      ∑ i : ι, ∑ j : ι, if ¬ good i then w i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : good i <;> simp only [h, not_true_eq_false, not_false_eq_true, if_false, if_true, hsymm j i]
  have hsum : (∑ i : ι, ∑ j : ι, if ¬ good i ∨ ¬ good j then ‖k i j‖ else 0) ≤
      2 * ∑ i : ι, ∑ j : ι, if ¬ good i then w i j else 0 := by
    calc
      _ ≤ ∑ i : ι, ∑ j : ι,
          ((if ¬ good i then w i j else 0) + (if ¬ good j then w i j else 0)) :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hterm i j))
      _ = _ := by simp_rw [Finset.sum_add_distrib]; rw [hswap]; ring
  have hbase := maskedPairing_difference_le f g k good μ B hμ hB hf hg
  calc
    _ ≤ μ * B ^ 2 * (∑ i : ι, ∑ j : ι, if ¬ good i ∨ ¬ good j then ‖k i j‖ else 0) := hbase
    _ ≤ μ * B ^ 2 * (2 * ∑ i : ι, ∑ j : ι, if ¬ good i then w i j else 0) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hμ (sq_nonneg _))
    _ = _ := by ring


end ArtinPrimitiveRoots.TypeII.PD
