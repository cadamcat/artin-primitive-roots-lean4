import ArtinPrimitiveRoots.Construction.Defs

namespace ArtinPrimitiveRoots.Construction

noncomputable def c4TestFunction (y : ℝ) : ℝ :=
  Real.smoothTransition (4 * y - 4) * Real.smoothTransition (8 - 4 * y)

theorem c4TestFunction_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c4TestFunction := by
  unfold c4TestFunction
  fun_prop

theorem c4TestFunction_isTestFunction : IsTestFunction c4TestFunction := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact c4TestFunction_contDiff
  · intro y hy
    simp only [Function.mem_support] at hy
    have h₁ : Real.smoothTransition (4 * y - 4) ≠ 0 := by
      intro h
      apply hy
      unfold c4TestFunction
      rw [h]
      simp
    have h₂ : Real.smoothTransition (8 - 4 * y) ≠ 0 := by
      intro h
      apply hy
      unfold c4TestFunction
      rw [h]
      simp
    have hy₁ : 0 < 4 * y - 4 := by
      by_contra h
      exact h₁ (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
    have hy₂ : 0 < 8 - 4 * y := by
      by_contra h
      exact h₂ (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
    change 1 < y ∧ y < 2
    constructor <;> linarith
  · intro y
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · intro y
    calc
      _ ≤ 1 * Real.smoothTransition (8 - 4 * y) :=
        mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) zero_le_one
      _ = 1 := by ring
  · apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (c4TestFunction_contDiff.continuous.intervalIntegrable _ _)
    · intro y hy
      have h₁ : 0 < 4 * y - 4 := by
        rcases hy with ⟨hylo, hyhi⟩
        linarith
      have h₂ : 0 < 8 - 4 * y := by
        rcases hy with ⟨hylo, hyhi⟩
        linarith
      exact mul_pos (Real.smoothTransition.pos_of_pos h₁)
        (Real.smoothTransition.pos_of_pos h₂)
    · norm_num

open ArtinPrimitiveRoots.TypeII

theorem c4_roughAbove_mul (m n : ℕ) (y : ℝ) :
    roughAbove (m * n) y ↔ roughAbove m y ∧ roughAbove n y := by
  constructor
  · intro h
    constructor
    · intro p hp hpm
      exact h p hp (dvd_mul_of_dvd_left hpm n)
    · intro p hp hpn
      exact h p hp (dvd_mul_of_dvd_right hpn m)
  · rintro ⟨hm, hn⟩ p hp hpmn
    rcases hp.dvd_mul.mp hpmn with hpm | hpn
    · exact hm p hp hpm
    · exact hn p hp hpn

end ArtinPrimitiveRoots.Construction
