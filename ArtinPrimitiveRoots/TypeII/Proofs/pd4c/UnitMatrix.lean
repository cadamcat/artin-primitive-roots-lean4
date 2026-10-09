import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.FiniteGram

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical

noncomputable section

/-- Entrywise unit bounds give the trivial finite matrix norm used on the Fourier tail. -/
theorem finite_unit_matrix_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (U : Finset β) (k : β → α → ℂ) (f : α → ℂ)
    (hk : ∀ n ∈ U, ∀ i ∈ T, ‖k n i‖ ≤ 1) :
    (∑ n ∈ U, ‖∑ i ∈ T, k n i*f i‖^2) ≤
      (T.card : ℝ)*(U.card : ℝ)*(∑ i ∈ T, ‖f i‖^2) := by
  have hgram (i : α) (hi : i ∈ T) (j : α) (hj : j ∈ T) :
      ‖∑ n ∈ U, star (k n i)*k n j‖ ≤ (U.card : ℝ) := by
    calc
      _ ≤ ∑ n ∈ U, ‖star (k n i)*k n j‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ U, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, norm_star]
        simpa only [one_mul] using mul_le_mul (hk n hn i hi) (hk n hn j hj)
          (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      _ = _ := by simp
  have hrow (i : α) (hi : i ∈ T) :
      (∑ j ∈ T, ‖∑ n ∈ U, star (k n i)*k n j‖) ≤
        (T.card : ℝ)*(U.card : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ T, (U.card : ℝ) :=
        Finset.sum_le_sum (fun j hj => hgram i hi j hj)
      _ = _ := by simp
  have hcol (j : α) (hj : j ∈ T) :
      (∑ i ∈ T, ‖∑ n ∈ U, star (k n i)*k n j‖) ≤
        (T.card : ℝ)*(U.card : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ T, (U.card : ℝ) :=
        Finset.sum_le_sum (fun i hi => hgram i hi j hj)
      _ = _ := by simp
  exact finite_gram_norm_bound T U k f ((T.card : ℝ)*(U.card : ℝ))
    (by positivity) hrow hcol

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
