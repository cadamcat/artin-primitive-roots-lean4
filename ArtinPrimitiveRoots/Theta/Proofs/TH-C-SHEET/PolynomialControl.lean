import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».CoshControl
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false
noncomputable section

open MeasureTheory
open ArtinPrimitiveRoots.A1

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

/-- Polynomial-weighted cosh density in the scale q = x cosh u. -/
def cubicPolynomialDensity (P : Polynomial ℝ) (x u : ℝ) : ℝ :=
  P.eval (x * Real.cosh u) * Real.exp (-x * Real.cosh u) *
    Real.cosh ((1 / 3 : ℝ) * u)

/-- Its integral; the following control supplies absolute integrability for x > 0. -/
def cubicPolynomialIntegral (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), cubicPolynomialDensity P x u

/-- A polynomial costs only a constant after splitting the exponential decay. -/
theorem bessel_cubic_polynomial_control (P : Polynomial ℝ) :
    ∃ D E F : ℝ, 0 ≤ D ∧ 0 ≤ E ∧ 0 ≤ F ∧
      (∀ q : ℝ, 0 ≤ q →
        ‖P.eval q‖ * Real.exp (-q) ≤ D * Real.exp (-q / 2)) ∧
      (∀ x : ℝ, 0 < x →
        IntegrableOn (cubicPolynomialDensity P x) (Set.Ioi 0)) ∧
      (∀ x : ℝ, 0 < x →
        ‖cubicPolynomialIntegral P x‖ ≤ E * x ^ (-(1 / 3 : ℝ))) ∧
      (∀ x : ℝ, 1 ≤ x →
        ‖cubicPolynomialIntegral P x‖ ≤ F * Real.exp (-x / 4)) := by
  obtain ⟨B, hB, hbase⟩ := bessel_cubic_cosh_control
  let D : ℝ := ∑ n ∈ P.support, ‖P.coeff n‖ * (2 ^ n * (n.factorial : ℝ))
  have hD : 0 ≤ D := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hpow (n : ℕ) (q : ℝ) (hq : 0 ≤ q) :
      q ^ n * Real.exp (-q) ≤ (2 ^ n * (n.factorial : ℝ)) * Real.exp (-q / 2) := by
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hp := (div_le_iff₀ hfac).mp
      (Real.pow_div_factorial_le_exp (q / 2) (by linarith : 0 ≤ q / 2) n)
    have he : Real.exp (q / 2) * Real.exp (-q) = Real.exp (-q / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      q ^ n * Real.exp (-q) = (2 ^ n * (q / 2) ^ n) * Real.exp (-q) := by
        rw [← mul_pow]
        congr 1
        ring
      _ ≤ (2 ^ n * (Real.exp (q / 2) * (n.factorial : ℝ))) * Real.exp (-q) := by
        gcongr
      _ = (2 ^ n * (n.factorial : ℝ)) * (Real.exp (q / 2) * Real.exp (-q)) := by ring
      _ = _ := by rw [he]
  have hpoly (q : ℝ) (hq : 0 ≤ q) :
      ‖P.eval q‖ * Real.exp (-q) ≤ D * Real.exp (-q / 2) := by
    have hp : ‖P.eval q‖ ≤ ∑ n ∈ P.support, ‖P.coeff n‖ * q ^ n := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
      calc
        ‖∑ n ∈ P.support, P.coeff n * q ^ n‖ ≤
            ∑ n ∈ P.support, ‖P.coeff n * q ^ n‖ := norm_sum_le _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hq n)]
    calc
      ‖P.eval q‖ * Real.exp (-q) ≤
          (∑ n ∈ P.support, ‖P.coeff n‖ * q ^ n) * Real.exp (-q) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = ∑ n ∈ P.support, ‖P.coeff n‖ * (q ^ n * Real.exp (-q)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ ≤ ∑ n ∈ P.support, ‖P.coeff n‖ *
          ((2 ^ n * (n.factorial : ℝ)) * Real.exp (-q / 2)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (hpow n q hq) (norm_nonneg _)
      _ = D * Real.exp (-q / 2) := by
        dsimp only [D]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n hn
        ring
  have hn (x : ℝ) (hx : 0 < x) (u : ℝ) :
      ‖cubicPolynomialDensity P x u‖ ≤ D *
        (Real.exp (-(x / 2) * Real.cosh u) * Real.cosh ((1 / 3 : ℝ) * u)) := by
    have hq : 0 ≤ x * Real.cosh u := (mul_pos hx (Real.cosh_pos u)).le
    have hh := mul_le_mul_of_nonneg_right (hpoly (x * Real.cosh u) hq)
      (Real.cosh_pos ((1 / 3 : ℝ) * u)).le
    have he : -(x * Real.cosh u) / 2 = -(x / 2) * Real.cosh u := by ring
    rw [he] at hh
    simpa only [cubicPolynomialDensity, norm_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.cosh_pos _).le, neg_mul, mul_assoc] using hh
  have hf (x : ℝ) (hx : 0 < x) :
      IntegrableOn (cubicPolynomialDensity P x) (Set.Ioi 0) := by
    have hc : Continuous (cubicPolynomialDensity P x) := by
      unfold cubicPolynomialDensity
      fun_prop
    apply ((hbase (x / 2) (by positivity)).1.const_mul D).mono' hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (hn x hx)
  have hscale (x d : ℝ) (hx : 0 < x) (hd : 0 < d) :
      (x / d) ^ (-(1 / 3 : ℝ)) = d ^ (1 / 3 : ℝ) * x ^ (-(1 / 3 : ℝ)) := by
    rw [Real.div_rpow hx.le hd.le, Real.rpow_neg hd.le]
    simp only [div_inv_eq_mul]
    ring
  have hsmall (x : ℝ) (hx : 0 < x) :
      ‖cubicPolynomialIntegral P x‖ ≤ D * besselK (1 / 3) (x / 2) := by
    calc
      ‖cubicPolynomialIntegral P x‖ ≤
          ∫ u in Set.Ioi (0 : ℝ), ‖cubicPolynomialDensity P x u‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi (0 : ℝ), D *
          (Real.exp (-(x / 2) * Real.cosh u) * Real.cosh ((1 / 3 : ℝ) * u)) := by
        apply integral_mono_ae (hf x hx).norm
          ((hbase (x / 2) (by positivity)).1.const_mul D)
        exact Filter.Eventually.of_forall (hn x hx)
      _ = _ := by rw [integral_const_mul]; rfl
  have hlarge (x : ℝ) (hx : 0 < x) :
      ‖cubicPolynomialIntegral P x‖ ≤
        (D * Real.exp (-x / 4)) * besselK (1 / 3) (x / 4) := by
    have hn' (u : ℝ) : ‖cubicPolynomialDensity P x u‖ ≤
        (D * Real.exp (-x / 4)) *
          (Real.exp (-(x / 4) * Real.cosh u) * Real.cosh ((1 / 3 : ℝ) * u)) := by
      have hxq : x ≤ x * Real.cosh u := by
        nlinarith [Real.one_le_cosh u]
      have he : Real.exp (-(x / 2) * Real.cosh u) ≤
          Real.exp (-x / 4) * Real.exp (-(x / 4) * Real.cosh u) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        ‖cubicPolynomialDensity P x u‖ ≤ D *
            (Real.exp (-(x / 2) * Real.cosh u) * Real.cosh ((1 / 3 : ℝ) * u)) := hn x hx u
        _ ≤ D * ((Real.exp (-x / 4) * Real.exp (-(x / 4) * Real.cosh u)) *
            Real.cosh ((1 / 3 : ℝ) * u)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right he (Real.cosh_pos _).le) hD
        _ = _ := by ring
    calc
      ‖cubicPolynomialIntegral P x‖ ≤
          ∫ u in Set.Ioi (0 : ℝ), ‖cubicPolynomialDensity P x u‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi (0 : ℝ), (D * Real.exp (-x / 4)) *
          (Real.exp (-(x / 4) * Real.cosh u) * Real.cosh ((1 / 3 : ℝ) * u)) := by
        apply integral_mono_ae (hf x hx).norm
          ((hbase (x / 4) (by positivity)).1.const_mul (D * Real.exp (-x / 4)))
        exact Filter.Eventually.of_forall hn'
      _ = _ := by rw [integral_const_mul]; rfl
  refine ⟨D, D * B * 2 ^ (1 / 3 : ℝ), D * B * 4 ^ (1 / 3 : ℝ),
    hD, by positivity, by positivity, hpoly, hf, ?_, ?_⟩
  · intro x hx
    calc
      ‖cubicPolynomialIntegral P x‖ ≤ D * besselK (1 / 3) (x / 2) := hsmall x hx
      _ ≤ D * (B * (x / 2) ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hbase (x / 2) (by positivity)).2.2 hD
      _ = _ := by rw [hscale x 2 hx (by norm_num)]; ring
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
    have hr : x ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
    calc
      ‖cubicPolynomialIntegral P x‖ ≤
          (D * Real.exp (-x / 4)) * besselK (1 / 3) (x / 4) := hlarge x hx0
      _ ≤ (D * Real.exp (-x / 4)) * (B * (x / 4) ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hbase (x / 4) (by positivity)).2.2 (by positivity)
      _ = (D * B * 4 ^ (1 / 3 : ℝ) * Real.exp (-x / 4)) *
          x ^ (-(1 / 3 : ℝ)) := by rw [hscale x 4 hx0 (by norm_num)]; ring
      _ ≤ _ := by
        simpa using mul_le_mul_of_nonneg_left hr
          (show 0 ≤ D * B * 4 ^ (1 / 3 : ℝ) * Real.exp (-x / 4) by positivity)


end ArtinPrimitiveRoots.Proofs.thsol_smooth
