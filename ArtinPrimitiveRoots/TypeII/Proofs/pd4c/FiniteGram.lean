import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Circle

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical

noncomputable section

/-- Finite Gram row and column bounds control the squared norm of the original matrix. -/
theorem finite_gram_norm_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (U : Finset β) (k : β → α → ℂ) (f : α → ℂ) (R : ℝ)
    (hR : 0 ≤ R)
    (hrow : ∀ i ∈ T, ∑ j ∈ T,
      ‖∑ n ∈ U, star (k n i) * k n j‖ ≤ R)
    (hcol : ∀ j ∈ T, ∑ i ∈ T,
      ‖∑ n ∈ U, star (k n i) * k n j‖ ≤ R) :
    (∑ n ∈ U, ‖∑ i ∈ T, k n i * f i‖ ^ 2) ≤
      R * (∑ i ∈ T, ‖f i‖ ^ 2) := by
  let G (i j : α) : ℂ := ∑ n ∈ U, star (k n i) * k n j
  have hnorm (z : ℂ) : ‖z‖ ^ 2 = (star z * z).re := by
    simp only [RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
      Complex.ofReal_re]
  have hpoint (n : β) : ‖∑ i ∈ T, k n i * f i‖ ^ 2 =
      (∑ i ∈ T, ∑ j ∈ T, star (f i) * f j * (star (k n i) * k n j)).re := by
    rw [hnorm]
    congr 1
    simp_rw [star_sum, Finset.sum_mul, Finset.mul_sum, star_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hswap :
      (∑ n ∈ U, ∑ i ∈ T, ∑ j ∈ T,
        star (f i) * f j * (star (k n i) * k n j)) =
      ∑ i ∈ T, ∑ j ∈ T, star (f i) * f j * G i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [G]
    exact (Finset.mul_sum _ _ _).symm
  have henergy : (∑ n ∈ U, ‖∑ i ∈ T, k n i * f i‖ ^ 2) =
      (∑ i ∈ T, ∑ j ∈ T, star (f i) * f j * G i j).re := by
    calc
      _ = (∑ n ∈ U, ∑ i ∈ T, ∑ j ∈ T,
          star (f i) * f j * (star (k n i) * k n j)).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun n hn => hpoint n
      _ = _ := congrArg Complex.re hswap
  have htri : (∑ n ∈ U, ‖∑ i ∈ T, k n i * f i‖ ^ 2) ≤
      ∑ i ∈ T, ∑ j ∈ T, ‖f i‖ * ‖f j‖ * ‖G i j‖ := by
    rw [henergy, Complex.re_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Complex.re_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      _ ≤ ‖star (f i) * f j * G i j‖ := Complex.re_le_norm _
      _ = _ := by simp only [norm_mul, norm_star]
  have hhalf : (∑ i ∈ T, ∑ j ∈ T, ‖f i‖ * ‖f j‖ * ‖G i j‖) ≤
      ∑ i ∈ T, ∑ j ∈ T, ((‖f i‖ ^ 2 + ‖f j‖ ^ 2) / 2) * ‖G i j‖ := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    nlinarith only [sq_nonneg (‖f i‖ - ‖f j‖)]
  have hsplit :
      (∑ i ∈ T, ∑ j ∈ T, ((‖f i‖ ^ 2 + ‖f j‖ ^ 2) / 2) * ‖G i j‖) =
      ((∑ i ∈ T, ∑ j ∈ T, ‖f i‖ ^ 2 * ‖G i j‖) +
        (∑ i ∈ T, ∑ j ∈ T, ‖f j‖ ^ 2 * ‖G i j‖)) / 2 := by
    calc
      _ = ∑ i ∈ T, ∑ j ∈ T,
          (‖f i‖ ^ 2 * ‖G i j‖ + ‖f j‖ ^ 2 * ‖G i j‖) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp only [← Finset.sum_div, Finset.sum_add_distrib]
  have hrows : (∑ i ∈ T, ∑ j ∈ T, ‖f i‖ ^ 2 * ‖G i j‖) ≤
      R * (∑ i ∈ T, ‖f i‖ ^ 2) := by
    calc
      _ = ∑ i ∈ T, ‖f i‖ ^ 2 * (∑ j ∈ T, ‖G i j‖) := by
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ T, ‖f i‖ ^ 2 * R := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hcols : (∑ i ∈ T, ∑ j ∈ T, ‖f j‖ ^ 2 * ‖G i j‖) ≤
      R * (∑ i ∈ T, ‖f i‖ ^ 2) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j ∈ T, ‖f j‖ ^ 2 * (∑ i ∈ T, ‖G i j‖) := by
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ T, ‖f j‖ ^ 2 * R := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hcol j hj) (sq_nonneg _)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  rw [hsplit] at hhalf
  exact htri.trans (hhalf.trans (by linarith only [hrows, hcols]))

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
