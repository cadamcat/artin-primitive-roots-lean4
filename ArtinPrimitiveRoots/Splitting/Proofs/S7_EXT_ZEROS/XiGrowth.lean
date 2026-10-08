import ArtinPrimitiveRoots.Splitting.Defs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.DeligneGrowth
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false

open scoped NumberField
open NumberField ArtinPrimitiveRoots.Splitting

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- Entire Xi with fixed shifted reciprocal archimedean factors. -/
noncomputable def xiGammaQuotient (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  dedekindXi K s * ((Complex.Gammaℝ (s + 8))⁻¹) ^ InfinitePlace.nrRealPlaces K *
    ((Complex.Gammaℂ (s + 4))⁻¹) ^ InfinitePlace.nrComplexPlaces K

/-- D2 and positive-strip digamma control supply the Xi quotient's strip growth. -/
theorem xiGammaQuotient_entire_and_growth
    (hdigamma : ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, 1 ≤ u.re → u.re ≤ 10 →
      ‖deriv Complex.Gamma u / Complex.Gamma u‖ ≤ C * Real.log (|u.im| + 2))
    (K : Type*) [Field K] [NumberField K] :
    Differentiable ℂ (xiGammaQuotient K) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -2 ≤ s.re → s.re ≤ 6 →
        ‖xiGammaQuotient K s‖ ≤ Real.exp (C * (‖s‖ + 1) ^ 2) := by
  have hspec := Classical.choose_spec (ArtinPrimitiveRoots.Hecke.dedekind_completed K)
  have hXi : Differentiable ℂ (dedekindXi K) := hspec.1
  have heq : ∀ s : ℂ, 1 < s.re → dedekindXi K s =
      s * (s - 1) * ArtinPrimitiveRoots.Hecke.dedekindPrefactor K s * dedekindZeta K s :=
    hspec.2.1
  let r1 : ℕ := InfinitePlace.nrRealPlaces K
  let r2 : ℕ := InfinitePlace.nrComplexPlaces K
  have hR : Differentiable ℂ (fun s : ℂ => ((Complex.Gammaℝ (s + 8))⁻¹) ^ r1) :=
    (Complex.differentiable_Gammaℝ_inv.comp
      (differentiable_id.add (differentiable_const (8 : ℂ)))).pow r1
  have hC : Differentiable ℂ (fun s : ℂ => ((Complex.Gammaℂ (s + 4))⁻¹) ^ r2) :=
    (Complex.differentiable_Gammaℂ_inv.comp
      (differentiable_id.add (differentiable_const (4 : ℂ)))).pow r2
  refine ⟨?_, ?_⟩
  · change Differentiable ℂ (fun s : ℂ => dedekindXi K s *
      ((Complex.Gammaℝ (s + 8))⁻¹) ^ r1 * ((Complex.Gammaℂ (s + 4))⁻¹) ^ r2)
    convert (hXi.mul hR).mul hC using 1
  obtain ⟨C0, hC0, hxi⟩ := ArtinPrimitiveRoots.Hecke.dedekind_order_one K (dedekindXi K) hXi heq
  obtain ⟨A, hA, harch⟩ := shifted_deligne_inverse_quadratic_growth hdigamma
  refine ⟨C0 + (r1 : ℝ) * A + (r2 : ℝ) * A + 1, by positivity, ?_⟩
  intro s hsa hsb
  have hlog : Real.log (‖s‖ + 2) ≤ ‖s‖ + 1 := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < ‖s‖ + 2 by positivity)
    linarith
  have hxiQ : ‖dedekindXi K s‖ ≤ Real.exp (C0 * (‖s‖ + 1) ^ 2) := by
    refine (hxi s).trans (Real.exp_le_exp.mpr ?_)
    calc
      C0 * (‖s‖ + 1) * Real.log (‖s‖ + 2) ≤ C0 * (‖s‖ + 1) * (‖s‖ + 1) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = C0 * (‖s‖ + 1) ^ 2 := by ring
  have hRpow : ‖(Complex.Gammaℝ (s + 8))⁻¹‖ ^ r1 ≤
      Real.exp (((r1 : ℝ) * A) * (‖s‖ + 1) ^ 2) := by
    calc
      ‖(Complex.Gammaℝ (s + 8))⁻¹‖ ^ r1 ≤
          (Real.exp (A * (‖s‖ + 1) ^ 2)) ^ r1 :=
        pow_le_pow_left₀ (norm_nonneg _) (harch s hsa hsb).1 r1
      _ = Real.exp (((r1 : ℝ) * A) * (‖s‖ + 1) ^ 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hCpow : ‖(Complex.Gammaℂ (s + 4))⁻¹‖ ^ r2 ≤
      Real.exp (((r2 : ℝ) * A) * (‖s‖ + 1) ^ 2) := by
    calc
      ‖(Complex.Gammaℂ (s + 4))⁻¹‖ ^ r2 ≤
          (Real.exp (A * (‖s‖ + 1) ^ 2)) ^ r2 :=
        pow_le_pow_left₀ (norm_nonneg _) (harch s hsa hsb).2 r2
      _ = Real.exp (((r2 : ℝ) * A) * (‖s‖ + 1) ^ 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hfirst : ‖dedekindXi K s‖ * ‖(Complex.Gammaℝ (s + 8))⁻¹‖ ^ r1 ≤
      Real.exp (C0 * (‖s‖ + 1) ^ 2) *
        Real.exp (((r1 : ℝ) * A) * (‖s‖ + 1) ^ 2) :=
    mul_le_mul hxiQ hRpow (by positivity) (Real.exp_pos _).le
  change ‖dedekindXi K s * ((Complex.Gammaℝ (s + 8))⁻¹) ^ r1 *
    ((Complex.Gammaℂ (s + 4))⁻¹) ^ r2‖ ≤ _
  simp only [norm_mul, norm_pow]
  calc
    ‖dedekindXi K s‖ * ‖(Complex.Gammaℝ (s + 8))⁻¹‖ ^ r1 *
        ‖(Complex.Gammaℂ (s + 4))⁻¹‖ ^ r2 ≤
        (Real.exp (C0 * (‖s‖ + 1) ^ 2) *
          Real.exp (((r1 : ℝ) * A) * (‖s‖ + 1) ^ 2)) *
          Real.exp (((r2 : ℝ) * A) * (‖s‖ + 1) ^ 2) :=
      mul_le_mul hfirst hCpow (by positivity) (by positivity)
    _ = Real.exp ((C0 + (r1 : ℝ) * A + (r2 : ℝ) * A) * (‖s‖ + 1) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((C0 + (r1 : ℝ) * A + (r2 : ℝ) * A + 1) * (‖s‖ + 1) ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (‖s‖ + 1)]

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
