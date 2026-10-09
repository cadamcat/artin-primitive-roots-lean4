import ArtinPrimitiveRoots.TypeII.Defs

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical

noncomputable section

/-- Bounded weighted endpoint factors transfer a counting kernel norm to the weighted norm. -/
theorem finite_weighted_diagonal_transfer {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (μ : ι → ℝ) (k : ι → ι → ℂ) (d e : ι → ℂ)
    (C D R : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hμ : ∀ i ∈ I, 0 ≤ μ i)
    (hd : ∀ i ∈ I, Real.sqrt (μ i)*‖d i‖ ≤ C)
    (he : ∀ i ∈ I, Real.sqrt (μ i)*‖e i‖ ≤ D)
    (hk : ∀ g : ι → ℂ,
      (∑ i ∈ I, ‖∑ j ∈ I, k i j*g j‖^2) ≤ R^2*(∑ j ∈ I, ‖g j‖^2))
    (f : ι → ℂ) :
    (∑ i ∈ I, μ i*‖d i*(∑ j ∈ I, k i j*(μ j : ℂ)*e j*f j)‖^2) ≤
      (C*D*R)^2*(∑ j ∈ I, μ j*‖f j‖^2) := by
  let g : ι → ℂ := fun j => (μ j : ℂ)*e j*f j
  have hdSq (i : ι) (hi : i ∈ I) : μ i*‖d i‖^2 ≤ C^2 := by
    calc
      _ = (Real.sqrt (μ i)*‖d i‖)^2 := by rw [mul_pow, Real.sq_sqrt (hμ i hi)]
      _ ≤ C^2 := pow_le_pow_left₀ (by positivity) (hd i hi) 2
  have heSq (j : ι) (hj : j ∈ I) : μ j*‖e j‖^2 ≤ D^2 := by
    calc
      _ = (Real.sqrt (μ j)*‖e j‖)^2 := by rw [mul_pow, Real.sq_sqrt (hμ j hj)]
      _ ≤ D^2 := pow_le_pow_left₀ (by positivity) (he j hj) 2
  have hinput (j : ι) (hj : j ∈ I) : ‖g j‖^2 ≤ D^2*(μ j*‖f j‖^2) := by
    calc
      _ = μ j*(μ j*‖e j‖^2)*‖f j‖^2 := by
        simp only [g, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hμ j hj), mul_pow]
        ring
      _ ≤ μ j*D^2*‖f j‖^2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (heSq j hj) (hμ j hj)) (sq_nonneg _)
      _ = _ := by ring
  have hinputSum : (∑ j ∈ I, ‖g j‖^2) ≤ D^2*(∑ j ∈ I, μ j*‖f j‖^2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => hinput j hj)
  have hrow (i : ι) :
      (∑ j ∈ I, k i j*(μ j : ℂ)*e j*f j) = ∑ j ∈ I, k i j*g j := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [g]
    ring
  have houtput (i : ι) (hi : i ∈ I) :
      μ i*‖d i*(∑ j ∈ I, k i j*g j)‖^2 ≤ C^2*‖∑ j ∈ I, k i j*g j‖^2 := by
    calc
      _ = (μ i*‖d i‖^2)*‖∑ j ∈ I, k i j*g j‖^2 := by rw [norm_mul, mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hdSq i hi) (sq_nonneg _)
  simp_rw [hrow]
  calc
    _ ≤ C^2*(∑ i ∈ I, ‖∑ j ∈ I, k i j*g j‖^2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i hi => houtput i hi)
    _ ≤ C^2*(R^2*(∑ j ∈ I, ‖g j‖^2)) :=
      mul_le_mul_of_nonneg_left (hk g) (sq_nonneg _)
    _ ≤ C^2*(R^2*(D^2*(∑ j ∈ I, μ j*‖f j‖^2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinputSum (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
