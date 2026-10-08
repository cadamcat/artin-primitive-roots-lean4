import ArtinPrimitiveRoots.Construction.Defs

namespace ArtinPrimitiveRoots.Construction

open Filter
open scoped Topology

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

theorem exists_small_completion_b (Cs Cd b₂ κ E : ℝ)
    (hCs : 0 < Cs) (hCd : 0 < Cd) (hb₂ : 0 < b₂)
    (hκ : 0 < κ) (hκsmall : κ < 1 / 100) (hE : 0 < E) :
    ∃ b : ℝ, 0 < b ∧ b < b₂ ∧ b < 1 / 2 - κ ∧ b < 1 / 100 ∧
      E / b * (Cs * Real.exp (-(1 / 20 : ℝ) / b) +
        Cd * Real.exp (-(1 / 20 : ℝ) / b)) < 1 / 5 := by
  have hdec : Tendsto (fun t : ℝ => t * Real.exp (-t / 20)) atTop (𝓝 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 : ℝ) (1 / 20 : ℝ) (by norm_num : (0 : ℝ) < 1 / 20)) using 1
    ext t
    congr 2
    · simp [Real.rpow_one]
    · ring
  have hdecConst : Tendsto
      (fun t : ℝ => E * (Cs + Cd) * (t * Real.exp (-t / 20))) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => E * (Cs + Cd)) atTop
        (𝓝 (E * (Cs + Cd))) := tendsto_const_nhds
    have h := hconst.mul hdec
    simpa [mul_assoc] using h
  have hEvent : ∀ᶠ t : ℝ in atTop,
      E * (Cs + Cd) * (t * Real.exp (-t / 20)) < 1 / 5 :=
    hdecConst.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 5))
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hEvent
  have hbUpper : 0 < 1 / 2 - κ := by linarith
  let U : ℝ := max (T + 1)
    (max (1 / b₂ + 1) (max (1 / (1 / 2 - κ) + 1) 101))
  have hU101 : 101 ≤ U := by dsimp [U]; exact le_trans (by norm_num) (le_max_right _ _)
  have hUpos : 0 < U := by linarith
  have hUT : T ≤ U := by
    dsimp [U]
    exact le_trans (by linarith) (le_max_left _ _)
  let b : ℝ := U⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  have hUb₂ : 1 / b₂ < U := by
    dsimp [U]
    have hle : 1 / b₂ + 1 ≤ max (1 / b₂ + 1) (max (1 / (1 / 2 - κ) + 1) 101) :=
      le_max_left _ _
    exact lt_of_lt_of_le (by linarith) (le_trans hle (le_max_right _ _))
  have hbLt₂ : b < b₂ := by
    change U⁻¹ < b₂
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ hUpos).2
    have hmul := (div_lt_iff₀ hb₂).1 hUb₂
    simpa [mul_comm] using hmul
  have hUbκ : 1 / (1 / 2 - κ) < U := by
    dsimp [U]
    have hle : 1 / (1 / 2 - κ) + 1 ≤
        max (1 / (1 / 2 - κ) + 1) 101 := le_max_left _ _
    exact lt_of_lt_of_le (by linarith)
      (le_trans hle (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hbLtκ : b < 1 / 2 - κ := by
    change U⁻¹ < 1 / 2 - κ
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ hUpos).2
    have hmul := (div_lt_iff₀ hbUpper).1 hUbκ
    simpa [mul_comm] using hmul
  have hbLt100 : b < 1 / 100 := by
    change U⁻¹ < 1 / 100
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ hUpos).2
    nlinarith [hU101]
  have hsmall := hT U hUT
  have hrewrite : E / b *
      (Cs * Real.exp (-(1 / 20 : ℝ) / b) + Cd * Real.exp (-(1 / 20 : ℝ) / b)) =
      E * (Cs + Cd) * (U * Real.exp (-U / 20)) := by
    dsimp [b]
    field_simp [ne_of_gt hUpos]
    <;> ring
  refine ⟨b, hb, hbLt₂, hbLtκ, hbLt100, ?_⟩
  rw [hrewrite]
  exact hsmall

end ArtinPrimitiveRoots.Construction
