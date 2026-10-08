import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Schur

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

/-- Weighted kernel reversal converts a row estimate of the reverse piece into a column estimate. -/
theorem pd4c_colSchur_of_kernelTranspose {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op rev : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (a D : ℝ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) (hD : 0 ≤ D)
    (htr : ∀ s t : MemPoint S.x K, MemValid F S s → memSize s ≤ B →
      MemValid F S t → memSize t ≤ B →
        memMeasure F S s * ‖memKernel op s t‖ ≤
          D * memMeasure F S t * ‖memKernel rev t s‖)
    (hrow : MemRowSchurLE F S B rev 1 a) : MemColSchurLE F S B op 1 (D * a) := by
  intro t ht hsize T hT
  have hr := hrow t ht hsize T hT
  simp only [one_pow, mul_one] at hr ⊢
  calc
    _ ≤ ∑ s ∈ T, D * memMeasure F S t * ‖memKernel rev t s‖ := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hv : MemValid F S s
      · exact htr s t hv (hT s hs) ht hsize
      · have hm : memMeasure F S s = 0 := by simp only [memMeasure, if_neg hv]
        rw [hm, zero_mul]
        exact mul_nonneg (mul_nonneg hD (hμ t)) (norm_nonneg _)
    _ = D * memMeasure F S t * ∑ s ∈ T, ‖memKernel rev t s‖ := by rw [Finset.mul_sum]
    _ ≤ D * memMeasure F S t * a := mul_le_mul_of_nonneg_left hr (mul_nonneg hD (hμ t))
    _ = _ := by ring

end

end ArtinPrimitiveRoots.TypeII.PD
