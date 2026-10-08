/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The proof below adapts DirichletCharacter.re_log_comb_nonneg' from Mathlib.
-/
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».Endpoints
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

set_option autoImplicit false

open Complex
open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

/-- The local positivity input for the Dedekind Euler product on the unit circle. -/
theorem euler_factor_three_four_one {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

/-- The classical 3–4–1 inequality for the Dedekind Euler product. -/
theorem dedekind_three_four_one (K : Type*) [Field K] [NumberField K]
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖NumberField.dedekindZeta K σ ^ 3 *
      NumberField.dedekindZeta K ((σ : ℂ) + Complex.I * t) ^ 4 *
      NumberField.dedekindZeta K ((σ : ℂ) + 2 * Complex.I * t)‖ := by
  classical
  let F : ℂ → HeightOneSpectrum (𝓞 K) → ℂ :=
    fun s P => (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹
  have hs₀ : 1 < (σ : ℂ).re := by simpa using hσ
  have hs₁ : 1 < ((σ : ℂ) + I * t).re := by simpa using hσ
  have hs₂ : 1 < ((σ : ℂ) + 2 * I * t).re := by simpa using hσ
  have hprod := ((TauCeti.dedekindZeta_eulerProduct_hasProd (K := K) hs₀).pow 3).mul
    ((TauCeti.dedekindZeta_eulerProduct_hasProd (K := K) hs₁).pow 4) |>.mul
    (TauCeti.dedekindZeta_eulerProduct_hasProd (K := K) hs₂)
  have hlocal (P : HeightOneSpectrum (𝓞 K)) :
      1 ≤ ‖F σ P ^ 3 * F ((σ : ℂ) + I * t) P ^ 4 *
        F ((σ : ℂ) + 2 * I * t) P‖ := by
    let n : ℕ := Ideal.absNorm P.asIdeal
    have hn : 1 < n := NumberField.HeightOneSpectrum.one_lt_absNorm P
    have hn₀ : 0 < n := by omega
    have hnℂ : (n : ℂ) ≠ 0 := by exact_mod_cast hn₀.ne'
    let a : ℝ := (n : ℝ) ^ (-σ)
    let z : ℂ := (n : ℂ) ^ (-(I * t))
    have ha₀ : 0 ≤ a := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have ha₁ : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hn) (by linarith)
    have hz : ‖z‖ = 1 := by
      dsimp [z]
      rw [Complex.norm_natCast_cpow_of_pos hn₀]
      simp
    have e₀ : (n : ℂ) ^ (-(σ : ℂ)) = (a : ℂ) := by
      simpa [a] using (Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)).symm
    have e₁ : (n : ℂ) ^ (-((σ : ℂ) + I * t)) = a * z := by
      rw [neg_add, Complex.cpow_add _ _ hnℂ, e₀]
    have e₂ : (n : ℂ) ^ (-((σ : ℂ) + 2 * I * t)) = a * z ^ 2 := by
      rw [neg_add, Complex.cpow_add _ _ hnℂ,
        show -(2 * I * (t : ℂ)) = (2 : ℕ) * (-(I * t)) by push_cast; ring,
        Complex.cpow_nat_mul, e₀]
    have hden {s : ℂ} (hs : 1 < s.re) : 1 - (n : ℂ) ^ (-s) ≠ 0 := by
      have hnorm : ‖(n : ℂ) ^ (-s)‖ < 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hn₀, Complex.neg_re]
        exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (by linarith)
      intro heq
      have heq' : (n : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp heq).symm
      rw [heq'] at hnorm
      norm_num at hnorm
    have hexp {s : ℂ} (hs : 1 < s.re) :
        (1 - (n : ℂ) ^ (-s))⁻¹ = exp (-log (1 - (n : ℂ) ^ (-s))) := by
      rw [Complex.exp_neg, Complex.exp_log (hden hs)]
    have hpos := euler_factor_three_four_one ha₀ ha₁ hz
    dsimp only [F]
    change 1 ≤ ‖(1 - (n : ℂ) ^ (-(σ : ℂ)))⁻¹ ^ 3 *
      (1 - (n : ℂ) ^ (-((σ : ℂ) + I * t)))⁻¹ ^ 4 *
      (1 - (n : ℂ) ^ (-((σ : ℂ) + 2 * I * t)))⁻¹‖
    rw [hexp hs₀, hexp hs₁, hexp hs₂, ← exp_nat_mul, ← exp_nat_mul,
      ← exp_add, ← exp_add, norm_exp, Real.one_le_exp_iff]
    simpa only [Nat.cast_ofNat, add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero,
      e₀, e₁, e₂]
      using hpos
  refine le_hasProd_of_le_prod hprod.norm fun S => ?_
  exact Finset.one_le_prod₀ fun P _ => hlocal P

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
