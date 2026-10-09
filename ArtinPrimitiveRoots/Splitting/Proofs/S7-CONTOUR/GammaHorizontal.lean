import ArtinPrimitiveRoots.Ext.SplittingInputs
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Ext.SplittingInputs

/-- Gamma's recurrence transfers the positive-strip bound to high points of the contour strip. -/
theorem gamma_horizontal_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ,
      z.re ∈ Set.Icc (-1 / 2 : ℝ) 2 → 1 ≤ |z.im| →
      ‖deriv Complex.Gamma z / Complex.Gamma z‖ ≤
        B * Real.log (2 + |z.im|) := by
  obtain ⟨C, hC, hstrip⟩ :=
    ext_digamma_strip (a := (1 / 2 : ℝ)) (b := 3) (by norm_num)
  let L : ℝ := Real.log 2
  have hL : 0 < L := Real.log_pos (by norm_num)
  let B : ℝ := C + 1 / L
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro z hRe him
  have hzim : z.im ≠ 0 := by
    intro h
    simp only [h, abs_zero] at him
    norm_num at him
  have hz : z ≠ 0 := by
    intro h
    apply hzim
    simp [h]
  have hGamma : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    apply hzim
    simp [h]
  have hlow : (1 / 2 : ℝ) ≤ (z + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hRe.1]
  have hupp : (z + 1).re ≤ 3 := by
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hRe.2]
  have hshift : ‖deriv Complex.Gamma (z + 1) / Complex.Gamma (z + 1)‖ ≤
      C * Real.log (2 + |z.im|) := by
    simpa only [Complex.add_im, Complex.one_im, add_zero, add_comm] using
      hstrip (z + 1) hlow hupp
  have hrec : deriv Complex.Gamma z / Complex.Gamma z =
      deriv Complex.Gamma (z + 1) / Complex.Gamma (z + 1) - 1 / z := by
    rw [Complex.deriv_Gamma_add_one z hz, Complex.Gamma_add_one z hz]
    field_simp [hz, hGamma] <;> ring
  have hnorm : 1 ≤ ‖z‖ := him.trans (Complex.abs_im_le_norm z)
  have hnormpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hnorm
  have hinv : ‖(1 : ℂ) / z‖ ≤ 1 := by
    rw [norm_div, norm_one]
    apply (div_le_iff₀ hnormpos).2
    simpa using hnorm
  have hlog : L ≤ Real.log (2 + |z.im|) := by
    apply Real.log_le_log (by norm_num : 0 < (2 : ℝ))
    linarith only [abs_nonneg z.im]
  have habsorb : 1 ≤ Real.log (2 + |z.im|) / L := by
    apply (le_div_iff₀ hL).2
    simpa using hlog
  calc
    ‖deriv Complex.Gamma z / Complex.Gamma z‖ =
        ‖deriv Complex.Gamma (z + 1) / Complex.Gamma (z + 1) - 1 / z‖ := by rw [hrec]
    _ ≤ ‖deriv Complex.Gamma (z + 1) / Complex.Gamma (z + 1)‖ + ‖(1 : ℂ) / z‖ :=
      norm_sub_le _ _
    _ ≤ C * Real.log (2 + |z.im|) + 1 := add_le_add hshift hinv
    _ ≤ C * Real.log (2 + |z.im|) + Real.log (2 + |z.im|) / L := by
      linarith only [habsorb]
    _ = B * Real.log (2 + |z.im|) := by dsimp [B]; ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
