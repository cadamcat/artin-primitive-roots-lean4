import ArtinPrimitiveRoots.Spec.Defs

/-! Smooth height cutoffs with a scale-normalized transition region. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

/-- A smooth step which is zero below `A` and one above `2A`. -/
def specGapHeightCutoff (A : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((t - A) / A)

theorem specGapHeightCutoff_isCuspCutoff {A : ℝ} (hA : 0 < A) :
    IsCuspCutoff A (specGapHeightCutoff A) := by
  constructor
  · exact Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const A)
  constructor
  · intro x y hxy
    apply Real.smoothTransition.monotone
    apply div_le_div_of_nonneg_right _ hA.le
    linarith
  constructor
  · intro t ht
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact hA.le
  · intro t ht
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hA]
    linarith

theorem specGapHeightCutoff_bounds {A : ℝ} (t : ℝ) :
    0 ≤ specGapHeightCutoff A t ∧ specGapHeightCutoff A t ≤ 1 := by
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem realSmoothTransition_deriv_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, ‖deriv Real.smoothTransition t‖ ≤ B := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    Real.smoothTransition.contDiff.continuous_deriv (show 1 ≤ (∞ : ℕ∞ω) by simp)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht0 : t < 0
  · have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] Real.smoothTransition := by
      filter_upwards [isOpen_Iio.mem_nhds ht0] with y hy
      exact (Real.smoothTransition.zero_of_nonpos hy.le).symm
    have hd : deriv Real.smoothTransition t = 0 := by
      simpa using heq.deriv_eq.symm
    simp [hd]
  · by_cases ht1 : 1 < t
    · have heq : (fun _ : ℝ => (1 : ℝ)) =ᶠ[𝓝 t] Real.smoothTransition := by
        filter_upwards [isOpen_Ioi.mem_nhds ht1] with y hy
        exact (Real.smoothTransition.one_of_one_le hy.le).symm
      have hd : deriv Real.smoothTransition t = 0 := by
        simpa using heq.deriv_eq.symm
      simp [hd]
    · have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_not_gt ht0, le_of_not_gt ht1⟩
      exact (hC t ht).trans (le_max_left _ _)

theorem specGapHeightCutoff_deriv_bound {A : ℝ} (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, ‖deriv (specGapHeightCutoff A) t‖ ≤ B / A := by
  obtain ⟨B, hB, hBound⟩ := realSmoothTransition_deriv_bound
  refine ⟨B, hB, ?_⟩
  intro t
  let y : ℝ := (t - A) / A
  have hinner : HasDerivAt (fun x : ℝ => (x - A) / A) (1 / A) t := by
    simpa using ((hasDerivAt_id t).sub_const A).div_const A
  have houterDiff : DifferentiableAt ℝ Real.smoothTransition y := by fun_prop
  have houter : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition y) y :=
    houterDiff.hasDerivAt
  have hcomp : deriv (specGapHeightCutoff A) t =
      deriv Real.smoothTransition y / A := by
    change deriv (Real.smoothTransition ∘ fun x : ℝ => (x - A) / A) t = _
    have h := houter.comp t hinner
    have h' := h.deriv
    simpa [y, div_eq_mul_inv, mul_assoc] using h'
  rw [hcomp, norm_div, Real.norm_of_nonneg hA.le]
  exact div_le_div_of_nonneg_right (hBound _) hA.le

theorem specGapHeightCutoff_deriv_bound_uniform :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A, 0 < A → ∀ t,
      ‖deriv (specGapHeightCutoff A) t‖ ≤ B / A := by
  obtain ⟨B, hB, hBound⟩ := realSmoothTransition_deriv_bound
  refine ⟨B, hB, ?_⟩
  intro A hA t
  let y : ℝ := (t - A) / A
  have hinner : HasDerivAt (fun x : ℝ => (x - A) / A) (1 / A) t := by
    simpa using ((hasDerivAt_id t).sub_const A).div_const A
  have houterDiff : DifferentiableAt ℝ Real.smoothTransition y := by fun_prop
  have houter : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition y) y :=
    houterDiff.hasDerivAt
  have hcomp : deriv (specGapHeightCutoff A) t =
      deriv Real.smoothTransition y / A := by
    change deriv (Real.smoothTransition ∘ fun x : ℝ => (x - A) / A) t = _
    have h := houter.comp t hinner
    have h' := h.deriv
    simpa [y, div_eq_mul_inv, mul_assoc] using h'
  rw [hcomp, norm_div, Real.norm_of_nonneg hA.le]
  exact div_le_div_of_nonneg_right (hBound _) hA.le

theorem specGapHeightCutoff_deriv_eq_zero_of_lt {A t : ℝ} (hA : 0 < A) (ht : t < A) :
    deriv (specGapHeightCutoff A) t = 0 := by
  have hcut := specGapHeightCutoff_isCuspCutoff hA
  have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] specGapHeightCutoff A := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with y hy
    exact (hcut.2.2.1 y hy.le).symm
  have hd := heq.deriv_eq.symm
  simpa [deriv_const] using hd

theorem specGapHeightCutoff_deriv_eq_zero_of_gt {A t : ℝ} (hA : 0 < A)
    (ht : 2 * A < t) : deriv (specGapHeightCutoff A) t = 0 := by
  have hcut := specGapHeightCutoff_isCuspCutoff hA
  have heq : (fun _ : ℝ => (1 : ℝ)) =ᶠ[𝓝 t] specGapHeightCutoff A := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with y hy
    exact (hcut.2.2.2 y hy.le).symm
  have hd := heq.deriv_eq.symm
  simpa [deriv_const] using hd

end ArtinPrimitiveRoots.A1.Spec

end
