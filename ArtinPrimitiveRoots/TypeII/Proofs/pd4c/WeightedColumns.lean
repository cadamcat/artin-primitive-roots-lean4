import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.KernelBounds

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

theorem pd4c_colSchur_of_kernelTranspose_weighted {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op rev : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (v a D : ℝ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) (hv : 0 ≤ v) (hD : 0 ≤ D)
    (htr : ∀ s t : MemPoint S.x K, MemValid F S s → memSize s ≤ B →
      MemValid F S t → memSize t ≤ B →
        memMeasure F S s * ‖memKernel op s t‖ ≤ D * memMeasure F S t * ‖memKernel rev t s‖)
    (hrow : MemRowSchurLE F S B rev v a) : MemColSchurLE F S B op v (D * a) := by
  intro t ht hsize T hT
  have hr := hrow t ht hsize T hT
  calc
    _ ≤ ∑ s ∈ T, D * memMeasure F S t * (‖memKernel rev t s‖ * v ^ memSize s) := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hvs : MemValid F S s
      · have h := mul_le_mul_of_nonneg_right (htr s t hvs (hT s hs) ht hsize) (pow_nonneg hv (memSize s))
        simpa only [mul_assoc] using h
      · have hm : memMeasure F S s = 0 := by simp only [memMeasure, if_neg hvs]
        rw [hm, zero_mul, zero_mul]
        exact mul_nonneg (mul_nonneg hD (hμ t)) (mul_nonneg (norm_nonneg _) (pow_nonneg hv _))
    _ = D * memMeasure F S t * ∑ s ∈ T, ‖memKernel rev t s‖ * v ^ memSize s := by rw [Finset.mul_sum]
    _ ≤ D * memMeasure F S t * (a * v ^ memSize t) := mul_le_mul_of_nonneg_left hr (mul_nonneg hD (hμ t))
    _ = _ := by ring

end

end ArtinPrimitiveRoots.TypeII.PD
