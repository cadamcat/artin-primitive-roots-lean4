import Mathlib

namespace ArtinPrimitiveRoots.Proofs.r_impl_muse

open Classical MeasureTheory
open scoped BigOperators

/-- The phase `exp (I * u * log y)` has norm one. -/
theorem phase_exp_norm (u y : ℝ) :
    ‖Complex.exp (Complex.I * u * Real.log y)‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (u : ℂ) * Real.log y).re = 0 := by simp
  rw [hre, Real.exp_zero]

/-- HasDerivAt for the phase in `y`, used for the Lipschitz bound below. -/
theorem phase_exp_hasDerivAt (u y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun z : ℝ => Complex.exp (Complex.I * u * Real.log z))
      (Complex.exp (Complex.I * u * Real.log y) * (Complex.I * u / y)) y := by
  have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy
  have harg : HasDerivAt (fun z : ℝ => Complex.I * (u : ℂ) * Real.log z)
      (Complex.I * (u : ℂ) * y⁻¹) y := hlog.ofReal_comp.const_mul _
  have hcomp := (Complex.hasDerivAt_exp _).comp y harg
  simpa [Function.comp_def, div_eq_mul_inv, Complex.ofReal_inv] using hcomp

/-- The phase is Lipschitz in `y` on `[M, 2M]` with constant `|u| / M`. -/
theorem phase_exp_lipschitz (u M : ℝ) (hM : 0 < M) (y₁ y₂ : ℝ)
    (h1 : M ≤ y₁) (h2 : y₁ ≤ 2 * M) (h3 : M ≤ y₂) (h4 : y₂ ≤ 2 * M) :
    ‖Complex.exp (Complex.I * u * Real.log y₁) -
      Complex.exp (Complex.I * u * Real.log y₂)‖ ≤ (|u| / M) * |y₁ - y₂| := by
  have hderiv : ∀ x ∈ Set.Icc M (2 * M),
      DifferentiableAt ℝ (fun z : ℝ => Complex.exp (Complex.I * u * Real.log z)) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hM (Set.mem_Icc.mp hx).1
    exact (phase_exp_hasDerivAt u x hxpos.ne').differentiableAt
  have hbound : ∀ x ∈ Set.Icc M (2 * M),
      ‖deriv (fun z : ℝ => Complex.exp (Complex.I * u * Real.log z)) x‖ ≤ |u| / M := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hM (Set.mem_Icc.mp hx).1
    have hxM : M ≤ x := (Set.mem_Icc.mp hx).1
    rw [(phase_exp_hasDerivAt u x hxpos.ne').deriv]
    have hnorm : ‖Complex.I * (u : ℂ) / (x : ℂ)‖ = |u| / |x| := by
      simp [norm_div, norm_mul]
    rw [norm_mul, phase_exp_norm, one_mul, hnorm, abs_of_pos hxpos]
    exact div_le_div_of_nonneg_left (abs_nonneg u) hM hxM
  have hconv : Convex ℝ (Set.Icc M (2 * M)) := convex_Icc M (2 * M)
  have hmem1 : y₁ ∈ Set.Icc M (2 * M) := Set.mem_Icc.mpr ⟨h1, h2⟩
  have hmem2 : y₂ ∈ Set.Icc M (2 * M) := Set.mem_Icc.mpr ⟨h3, h4⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbound hconv hmem1 hmem2
  simpa [Real.norm_eq_abs, norm_sub_rev, abs_sub_comm] using h

/-- Finite chains telescope: the sum over the last set is the sum over the first
plus the successive differences. The induction step normalizes its beta-redex
by `rfl` before the linear combination. -/
theorem sum_chain_decomp (F : ℕ → Finset ℕ) (f : ℕ → ℂ) (N : ℕ)
    (hsub : ∀ i, i < N → F i ⊆ F (i + 1)) :
    ∑ n ∈ F N, f n = ∑ n ∈ F 0, f n +
      ∑ i ∈ Finset.range N, (∑ n ∈ F (i + 1), f n - ∑ n ∈ F i, f n) := by
  revert hsub
  induction N with
  | zero =>
    intro hsub
    simp
  | succ k ih =>
    intro hsub
    have ih' := ih (fun i hi => hsub i (lt_of_lt_of_le hi (Nat.le_succ k)))
    rw [Finset.sum_range_succ]
    linear_combination ih'

/-- Summation by parts on `range (N+1)` with an explicit boundary term. -/
theorem summation_by_parts (G D : ℕ → ℂ) (N : ℕ) :
    G 1 * D 0 + ∑ i ∈ Finset.range (N + 1), G (i + 1) * (D (i + 1) - D i) =
      G (N + 1) * D (N + 1) - ∑ i ∈ Finset.Ioo 0 (N + 1), D i * (G (i + 1) - G i) := by
  induction N with
  | zero =>
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
    simp only [zero_add]
    have hIoo : Finset.Ioo (0 : ℕ) 1 = ∅ := by decide
    rw [hIoo, Finset.sum_empty]
    ring
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hIoo : Finset.Ioo 0 (k + 1 + 1) = insert (k + 1) (Finset.Ioo 0 (k + 1)) := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    rw [hIoo, Finset.sum_insert (by simp)]
    linear_combination ih

end ArtinPrimitiveRoots.Proofs.r_impl_muse
