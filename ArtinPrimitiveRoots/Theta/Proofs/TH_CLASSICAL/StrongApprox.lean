import ArtinPrimitiveRoots.Theta.Cover
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Arithmetic

set_option autoImplicit false
open scoped Classical MatrixGroups Topology
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

/-- A fixed alternating word of four elementary matrices represents every SL2 matrix. -/
theorem th_classical_sl_elementary_factorization {K : Type} [Field K] (g : SL(2, K)) :
    ∃ a b c d : K, Matrix.SpecialLinearGroup.toGL g =
      upperM K a * lowerM K b * upperM K c * lowerM K d := by
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with
  | h A B C D hdet =>
    by_cases hB : B = 0
    · have hAD : A * D = 1 := by simpa only [hB, zero_mul, sub_zero] using hdet
      have hA : A ≠ 0 := left_ne_zero_of_mul_eq_one hAD
      have hD : D = 1 / A := by
        apply (eq_div_iff hA).mpr
        simpa only [mul_comm] using hAD
      refine ⟨1, A - 1, -1 / A, A * (C - (A - 1)), ?_⟩
      apply Units.ext
      change !![A, B; C, D] = _
      ext i j
      fin_cases i <;> fin_cases j
      all_goals
        simp [upperM, lowerM, Matrix.mul_apply, Fin.sum_univ_two, hB, hD]
        <;> field_simp [hA]
        <;> ring
        <;> simp
    · have hC : C = (A * D - 1) / B := by
        apply (eq_div_iff hB).mpr
        linear_combination -hdet
      refine ⟨0, (D - 1) / B, B, (A - 1) / B, ?_⟩
      apply Units.ext
      change !![A, B; C, D] = _
      ext i j
      fin_cases i <;> fin_cases j
      all_goals
        simp [upperM, lowerM, Matrix.mul_apply, Fin.sum_univ_two, hC]
        <;> field_simp [hB]
        <;> ring
        <;> simp

end ArtinPrimitiveRoots.A1.Theta
