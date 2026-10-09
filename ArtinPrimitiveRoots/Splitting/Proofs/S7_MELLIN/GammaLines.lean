import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».GammaHorizontal

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Ext.SplittingInputs

/-- The four Gamma arguments in the functional equation have a uniform line bound. -/
theorem gamma_reflection_line_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ,
      (z.re = (-1 / 2 : ℝ) ∨ z.re = (-1 / 4 : ℝ) ∨
        z.re = (3 / 4 : ℝ) ∨ z.re = (3 / 2 : ℝ)) →
      ‖deriv Complex.Gamma z / Complex.Gamma z‖ ≤
        B * Real.log (2 + |z.im|) := by
  obtain ⟨C, hC, hstrip⟩ :=
    ext_digamma_strip (a := (1 / 2 : ℝ)) (b := (5 / 2 : ℝ)) (by norm_num)
  let L : ℝ := Real.log 2
  have hL : 0 < L := Real.log_pos (by norm_num)
  let B : ℝ := C + 4 / L
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro z hRe
  have hlow : -1 < z.re := by
    rcases hRe with h | h | h | h <;> norm_num [h]
  have hre0 : z.re ≠ 0 := by
    rcases hRe with h | h | h | h <;> norm_num [h]
  have hz : z ≠ 0 := by
    intro h
    exact hre0 (by simp [h])
  have hGamma : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m heq
    by_cases hm : m = 0
    · exact hz (by simpa only [hm, Nat.cast_zero, neg_zero] using heq)
    · have hmreal : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      have heqre : z.re = -(m : ℝ) := by simpa using congrArg Complex.re heq
      linarith
  have hshiftRe : (z + 1).re ∈ Set.Icc (1 / 2 : ℝ) (5 / 2) := by
    rcases hRe with h | h | h | h <;> norm_num [h]
  have hshift : ‖deriv Complex.Gamma (z + 1) / Complex.Gamma (z + 1)‖ ≤
      C * Real.log (2 + |z.im|) := by
    simpa only [Complex.add_im, Complex.one_im, add_zero, add_comm] using
      hstrip (z + 1) hshiftRe.1 hshiftRe.2
  have hrec : deriv Complex.Gamma z / Complex.Gamma z =
      deriv Complex.Gamma (z + 1) / Complex.Gamma (z + 1) - 1 / z := by
    rw [Complex.deriv_Gamma_add_one z hz, Complex.Gamma_add_one z hz]
    field_simp [hz, hGamma]
    <;> ring
  have habs : (1 / 4 : ℝ) ≤ |z.re| := by
    rcases hRe with h | h | h | h <;> norm_num [h]
  have hnorm : (1 / 4 : ℝ) ≤ ‖z‖ := habs.trans (Complex.abs_re_le_norm z)
  have hnormpos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hnorm
  have hinv : ‖(1 : ℂ) / z‖ ≤ 4 := by
    rw [norm_div, norm_one]
    apply (div_le_iff₀ hnormpos).2
    nlinarith
  have hlog : L ≤ Real.log (2 + |z.im|) :=
    Real.log_le_log (by norm_num : 0 < (2 : ℝ)) (by linarith [abs_nonneg z.im])
  have habsorb : 4 ≤ (4 / L) * Real.log (2 + |z.im|) := by
    have h := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (4 : ℝ) / L)
    have he : (4 / L) * L = (4 : ℝ) := by field_simp [hL.ne']
    rwa [he] at h
  calc
    ‖deriv Complex.Gamma z / Complex.Gamma z‖ =
        ‖deriv Complex.Gamma (z + 1) / Complex.Gamma (z + 1) - 1 / z‖ := by rw [hrec]
    _ ≤ ‖deriv Complex.Gamma (z + 1) / Complex.Gamma (z + 1)‖ + ‖(1 : ℂ) / z‖ :=
      norm_sub_le _ _
    _ ≤ C * Real.log (2 + |z.im|) + 4 := add_le_add hshift hinv
    _ ≤ C * Real.log (2 + |z.im|) + (4 / L) * Real.log (2 + |z.im|) :=
      add_le_add le_rfl habsorb
    _ = B * Real.log (2 + |z.im|) := by dsimp [B]; ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
