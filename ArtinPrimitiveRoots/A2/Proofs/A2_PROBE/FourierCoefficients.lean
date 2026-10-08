import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries

set_option autoImplicit false
open MeasureTheory
open scoped Classical Interval Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

/-- Twice differentiable interval families with matching endpoint values and derivatives
have a common summable Fourier-coefficient majorant whenever the function and second
derivative have uniform bounds. -/
theorem fourierCoeffOn_uniform_summable {ι : Type*}
    (lo hi : ℝ) (hlohi : lo < hi)
    (f0 f1 f2 : ι → ℝ → ℂ) (M0 M2 : ℝ)
    (hM0 : 0 ≤ M0) (hM2 : 0 ≤ M2)
    (hderiv0 : ∀ i x, x ∈ Set.uIcc lo hi → HasDerivAt (f0 i) (f1 i x) x)
    (hderiv1 : ∀ i x, x ∈ Set.uIcc lo hi → HasDerivAt (f1 i) (f2 i x) x)
    (hcont2 : ∀ i, ContinuousOn (f2 i) (Set.uIcc lo hi))
    (hperiod0 : ∀ i, f0 i hi = f0 i lo)
    (hperiod1 : ∀ i, f1 i hi = f1 i lo)
    (hbound0 : ∀ i x, x ∈ Set.uIcc lo hi → ‖f0 i x‖ ≤ M0)
    (hbound2 : ∀ i x, x ∈ Set.uIcc lo hi → ‖f2 i x‖ ≤ M2) :
    ∃ bound : ℤ → ℝ, (∀ n, 0 ≤ bound n) ∧ Summable bound ∧
      ∀ i n, ‖fourierCoeffOn hlohi (f0 i) n‖ ≤ bound n := by
  classical
  have hT : 0 < hi - lo := sub_pos.mpr hlohi
  have hcoeff (f : ℝ → ℂ) (M : ℝ)
      (hbound : ∀ x ∈ Set.uIcc lo hi, ‖f x‖ ≤ M) (n : ℤ) :
      ‖fourierCoeffOn hlohi f n‖ ≤ M := by
    have hInt : ‖∫ x in lo..hi,
        fourier (-n) (x : AddCircle (hi - lo)) • f x‖ ≤ M * |hi - lo| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      exact hbound x (Set.uIoc_subset_uIcc hx)
    rw [fourierCoeffOn_eq_integral, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hT)]
    calc
      _ ≤ (1 / (hi - lo)) * (M * |hi - lo|) :=
        mul_le_mul_of_nonneg_left hInt (one_div_nonneg.mpr hT.le)
      _ = M := by rw [abs_of_pos hT]; field_simp
  let D : ℝ := ((hi - lo) / (2 * Real.pi)) ^ 2 * M2
  let bound : ℤ → ℝ := fun n => (if n = 0 then M0 else 0) + D / (n : ℝ) ^ 2
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _) hM2
  have hsum : Summable bound := by
    have hzero : Summable (fun n : ℤ => if n = 0 then M0 else 0) :=
      (hasSum_ite_eq 0 M0).summable
    have htail : Summable (fun n : ℤ => D / (n : ℝ) ^ 2) := by
      convert (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left D using 1
      ext n
      ring
    exact hzero.add htail
  refine ⟨bound, ?_, hsum, ?_⟩
  · intro n
    dsimp [bound]
    split_ifs <;> positivity
  · intro i n
    by_cases hn : n = 0
    · simpa [bound, hn] using hcoeff (f0 i) M0 (hbound0 i) n
    have hcont1 : ContinuousOn (f1 i) (Set.uIcc lo hi) :=
      fun x hx => (hderiv1 i x hx).continuousAt.continuousWithinAt
    have hfirst := fourierCoeffOn_of_hasDerivAt hlohi hn (hderiv0 i)
      hcont1.intervalIntegrable
    have hsecond := fourierCoeffOn_of_hasDerivAt hlohi hn (hderiv1 i)
      (hcont2 i).intervalIntegrable
    let c : ℂ := ((hi - lo : ℝ) : ℂ) / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
    have hfirst' : fourierCoeffOn hlohi (f0 i) n =
        c * fourierCoeffOn hlohi (f1 i) n := by
      rw [hfirst, hperiod0]
      simp [c, div_eq_mul_inv, inv_neg]
      ring
    have hsecond' : fourierCoeffOn hlohi (f1 i) n =
        c * fourierCoeffOn hlohi (f2 i) n := by
      rw [hsecond, hperiod1]
      simp [c, div_eq_mul_inv, inv_neg]
      ring
    have hnNorm : ‖(n : ℂ)‖ = |(n : ℝ)| := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    have hcNorm : ‖c‖ = (hi - lo) / (2 * Real.pi * |(n : ℝ)|) := by
      simp only [c, norm_div, norm_mul, Complex.norm_real,
        Complex.norm_ofNat, Complex.norm_I, mul_one, hnNorm, Real.norm_eq_abs,
        abs_of_pos hT, abs_of_pos Real.pi_pos]
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hnorm : ‖fourierCoeffOn hlohi (f0 i) n‖ ≤ D / (n : ℝ) ^ 2 := by
      calc
        _ = ((hi - lo) / (2 * Real.pi * |(n : ℝ)|)) ^ 2 *
            ‖fourierCoeffOn hlohi (f2 i) n‖ := by
              rw [hfirst', hsecond', norm_mul, norm_mul, hcNorm]
              ring
        _ ≤ ((hi - lo) / (2 * Real.pi * |(n : ℝ)|)) ^ 2 * M2 :=
          mul_le_mul_of_nonneg_left (hcoeff (f2 i) M2 (hbound2 i) n) (sq_nonneg _)
        _ = D / (n : ℝ) ^ 2 := by
          dsimp [D]
          field_simp [Real.pi_ne_zero, hnReal, abs_ne_zero.mpr hnReal]
          rw [sq_abs]
          ring
    simpa [bound, hn] using hnorm

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
