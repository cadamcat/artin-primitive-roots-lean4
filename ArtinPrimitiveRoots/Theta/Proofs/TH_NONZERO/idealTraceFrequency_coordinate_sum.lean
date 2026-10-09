import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_pairing

set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F]
variable (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ)

/-- In real ideal-basis coordinates, the archimedean trace pairing is
the negative dot product with the integer Fourier index. -/
theorem idealTraceFrequency_coordinate_sum [Fintype (Module.Free.ChooseBasisIndex ℤ I)]
    (n : Module.Free.ChooseBasisIndex ℤ I → ℤ)
    (x : Module.Free.ChooseBasisIndex ℤ I → ℝ) :
    (2 : ℝ) * ∑ w : InfinitePlace F,
      ((w.embedding (idealTraceFrequency F I n)) *
        ((idealArchBasis F I).equivFun.symm x w)).re =
        -(∑ i, (n i : ℝ) * x i) := by
  have hw (w : InfinitePlace F) :
      ((w.embedding (idealTraceFrequency F I n)) *
        ((idealArchBasis F I).equivFun.symm x w)).re =
      ∑ i, x i * ((w.embedding (idealTraceFrequency F I n)) *
        (idealArchBasis F I i w)).re := by
    rw [Basis.equivFun_symm_apply]
    simp [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hw]
  rw [Finset.sum_comm, Finset.mul_sum]
  calc
    ∑ i, 2 * ∑ w : InfinitePlace F,
        x i * ((w.embedding (idealTraceFrequency F I n)) *
          (idealArchBasis F I i w)).re =
      ∑ i, x i * (2 * ∑ w : InfinitePlace F,
        ((w.embedding (idealTraceFrequency F I n)) *
          (idealArchBasis F I i w)).re) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum]
        ring
    _ = ∑ i, x i * -(n i : ℝ) := by
      simp_rw [idealTraceFrequency_pairing]
    _ = -(∑ i, (n i : ℝ) * x i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end ArtinPrimitiveRoots.A1.Theta
