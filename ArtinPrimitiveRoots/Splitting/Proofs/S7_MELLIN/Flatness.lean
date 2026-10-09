import Mathlib

set_option autoImplicit false

open scoped Topology
open Filter

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

/-- Every derivative of a smooth positive test has arbitrary polynomial flatness at zero. -/
theorem test_flat_bound (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      Function.support f ⊆ Set.Ioi 0) (k N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv k f t| ≤ B * t ^ N := by
  have hsmooth (j : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iteratedDeriv j f) := by
    induction j with
    | zero => simpa using hf.1
    | succ j hj =>
      rw [iteratedDeriv_succ]
      exact (contDiff_infty_iff_deriv.mp hj).2
  have hzeroNeg (j : ℕ) : ∀ x : ℝ, x < 0 → iteratedDeriv j f x = 0 := by
    induction j with
    | zero =>
      intro x hx
      simp only [iteratedDeriv_zero]
      by_contra h
      have hpos := hf.2.2 (show x ∈ Function.support f from h)
      exact (not_lt_of_ge hx.le) (Set.mem_Ioi.mp hpos)
    | succ j hj =>
      intro x hx
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv j f =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
        filter_upwards [isOpen_Iio.eventually_mem
          (show x ∈ Set.Iio (0 : ℝ) from hx)] with y hy
        exact hj y (Set.mem_Iio.mp hy)
      rw [heq.deriv_eq]
      simp
  have hzeroAt (j : ℕ) : iteratedDeriv j f 0 = 0 := by
    have hclosed : IsClosed {x : ℝ | iteratedDeriv j f x = 0} :=
      isClosed_eq (hsmooth j).continuous continuous_const
    have hsub : Set.Iio (0 : ℝ) ⊆ {x : ℝ | iteratedDeriv j f x = 0} :=
      fun x hx => hzeroNeg j x hx
    have hmem : (0 : ℝ) ∈ closure (Set.Iio (0 : ℝ)) := by
      rw [closure_Iio]
      exact Set.mem_Iic.mpr le_rfl
    exact closure_minimal hsub hclosed hmem
  have hzG (j : ℕ) : iteratedDeriv j (iteratedDeriv k f) 0 = 0 := by
    simpa only [iteratedDeriv_eq_iterate, Function.iterate_add_apply] using hzeroAt (j + k)
  cases N with
  | zero =>
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hsmooth k).continuous.abs.continuousOn
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro t ht
    simpa using (hB (Set.mem_image_of_mem (fun x => |iteratedDeriv k f x|) ht)).trans
      (le_max_left B 0)
  | succ n =>
    obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
      (f := iteratedDeriv k f) (a := (0 : ℝ)) (b := 1) (n := n) (by norm_num)
      (((hsmooth k).of_le (by simp)).contDiffOn)
    have hwithin (j : ℕ) :
        iteratedDerivWithin j (iteratedDeriv k f) (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
        (((hsmooth k).of_le (show (j : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffAt)
        (by norm_num)]
      exact hzG j
    have hpoly (t : ℝ) :
        taylorWithinEval (iteratedDeriv k f) n (Set.Icc (0 : ℝ) 1) 0 t = 0 := by
      rw [taylor_within_apply]
      simp only [hwithin, smul_zero, Finset.sum_const_zero]
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro t ht
    have h := hC t ht
    rw [hpoly, sub_zero, Real.norm_eq_abs, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg ht.1 _))

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
