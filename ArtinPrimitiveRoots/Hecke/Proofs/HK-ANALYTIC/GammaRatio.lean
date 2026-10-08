import ArtinPrimitiveRoots.Hecke.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Complex MeasureTheory intervalIntegral Set
open scoped Real

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.HK_ANALYTIC

private def betaKernel (u v : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)

private def betaKernelReal (a b x : ℝ) : ℝ :=
  x ^ (a - 1) * (1 - x) ^ (b - 1)

private theorem betaKernel_norm_eq {a b t x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖betaKernel ((a : ℂ) + t * Complex.I) (b : ℂ) x‖ = betaKernelReal a b x := by
  rw [betaKernel, betaKernelReal, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hx0)]
  have hbase : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
  rw [hbase,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (sub_pos.mpr hx1))]
  simp [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.mul_re]

private theorem betaKernel_norm_integral_eq {a b t : ℝ} :
    ∫ x in (0:ℝ)..1, ‖betaKernel ((a : ℂ) + t * Complex.I) (b : ℂ) x‖ =
      ∫ x in (0:ℝ)..1, betaKernelReal a b x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (1:ℝ)] with x hx1 hx
  have hx' : x ∈ Set.Ioc (0:ℝ) 1 := by
    simpa only [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
  have hx0' : 0 < x := hx'.1
  have hx1' : x < 1 := lt_of_le_of_ne hx'.2 hx1
  exact betaKernel_norm_eq hx0' hx1'

private theorem betaRealKernel_integral_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0:ℝ)..1, betaKernelReal a b x) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have hβ := Complex.betaIntegral_eq_Gamma_mul_div
    (u := (a : ℂ)) (v := (b : ℂ)) (by simpa using ha) (by simpa using hb)
  have hcast :
      ((∫ x in (0:ℝ)..1, betaKernelReal a b x : ℝ) : ℂ) =
        Complex.betaIntegral (a : ℂ) (b : ℂ) := by
    rw [Complex.betaIntegral]
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0:ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
    have hx0 : 0 ≤ x := hx'.1
    have hx1 : 0 ≤ 1 - x := by linarith [hx'.2]
    simp only [betaKernelReal]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0,
      Complex.ofReal_sub, Complex.ofReal_cpow hx1]
    congr 1 <;> simp
  have hgamma : Complex.betaIntegral (a : ℂ) (b : ℂ) =
      ((Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) : ℝ) : ℂ) := by
    rw [hβ, ← Complex.ofReal_add, Complex.Gamma_ofReal,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    simp only [Complex.ofReal_mul, Complex.ofReal_div]
  have hre := congrArg Complex.re hcast
  rw [hgamma] at hre
  simpa using hre

/-- A beta-integral estimate for a vertical quotient of Gamma functions. -/
theorem gamma_positive_ratio_le (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
      Complex.Gamma ((a + b : ℂ) + t * Complex.I)‖ ≤
      Real.Gamma a / Real.Gamma (a + b) := by
  let u : ℂ := (a : ℂ) + t * Complex.I
  let v : ℂ := b
  have hu : 0 < u.re := by simpa [u] using ha
  have hv : 0 < v.re := by simpa [v] using hb
  have huv : 0 < (u + v).re := by
    simpa [u, v] using add_pos ha hb
  have hΓv : Complex.Gamma v ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hv
  have hΓsum : Complex.Gamma (u + v) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos huv
  have hratio : Complex.Gamma u / Complex.Gamma (u + v) =
      Complex.betaIntegral u v / Complex.Gamma v := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div u v hu hv]
    field_simp [hΓsum, hΓv]
  have hkernelInt := betaKernel_norm_integral_eq (a := a) (b := b) (t := t)
  have hbetaNorm : ‖Complex.betaIntegral u v‖ ≤
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
    simp only [u, v, Complex.betaIntegral]
    calc
      ‖∫ x in (0:ℝ)..1, betaKernel ((a : ℂ) + t * Complex.I) (b : ℂ) x‖
          ≤ ∫ x in (0:ℝ)..1,
              ‖betaKernel ((a : ℂ) + t * Complex.I) (b : ℂ) x‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ = ∫ x in (0:ℝ)..1, betaKernelReal a b x := hkernelInt
      _ = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) :=
        betaRealKernel_integral_eq ha hb
  have hGammaReal : ‖Complex.Gamma v‖ = Real.Gamma b := by
    rw [show v = (b : ℂ) by rfl, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos hb)]
  have hGammaRealPos : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  calc
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
        Complex.Gamma ((a + b : ℂ) + t * Complex.I)‖ =
        ‖Complex.Gamma u / Complex.Gamma (u + v)‖ := by
          congr 2 <;> simp [u, v] <;> ring
    _ =
        ‖Complex.betaIntegral u v / Complex.Gamma v‖ := congrArg norm hratio
    _ = ‖Complex.betaIntegral u v‖ / ‖Complex.Gamma v‖ := norm_div _ _
    _ = ‖Complex.betaIntegral u v‖ / Real.Gamma b := by rw [hGammaReal]
    _ ≤ (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) / Real.Gamma b :=
      div_le_div_of_nonneg_right hbetaNorm hGammaRealPos.le
    _ = Real.Gamma a / Real.Gamma (a + b) := by field_simp

private theorem gamma_norm_conj_eq (a t : ℝ) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I)‖ =
      ‖Complex.Gamma ((a : ℂ) - t * Complex.I)‖ := by
  calc
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I)‖ =
        ‖Complex.Gamma ((starRingEnd ℂ) ((a : ℂ) - t * Complex.I))‖ := by
          congr 2 <;> simp
    _ = ‖(starRingEnd ℂ) (Complex.Gamma ((a : ℂ) - t * Complex.I))‖ := by
          rw [Complex.Gamma_conj]
    _ = _ := norm_star _

private theorem gamma_ratio_conj_norm (a b t : ℝ) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
        Complex.Gamma ((b : ℂ) + t * Complex.I)‖ =
      ‖Complex.Gamma ((a : ℂ) - t * Complex.I) /
        Complex.Gamma ((b : ℂ) - t * Complex.I)‖ := by
  rw [norm_div, norm_div, gamma_norm_conj_eq a t, gamma_norm_conj_eq b t]

private theorem gamma_negative_ratio_le (δ t : ℝ) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) :
    ‖Complex.Gamma ((1 - (-δ + t * Complex.I)) : ℂ) /
        Complex.Gamma ((-δ + t * Complex.I) : ℂ)‖ ≤
      (Real.Gamma (1 + δ) / Real.Gamma (2 - δ)) * (2 + |t|) ^ 2 := by
  let s : ℂ := (-δ : ℂ) + t * Complex.I
  have hδsmall : δ < 1 := by linarith
  have hrec := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s
  have hratio : Complex.Gamma (1 - s) / Complex.Gamma s =
      s * (Complex.Gamma (1 - s) / Complex.Gamma (s + 1)) := by
    calc
      Complex.Gamma (1 - s) / Complex.Gamma s =
          Complex.Gamma (1 - s) * (Complex.Gamma s)⁻¹ := by rw [div_eq_mul_inv]
      _ = Complex.Gamma (1 - s) *
          (s * (Complex.Gamma (s + 1))⁻¹) := by rw [hrec]
      _ = s * (Complex.Gamma (1 - s) / Complex.Gamma (s + 1)) := by
          rw [div_eq_mul_inv]
          ring
  have hargs : 1 - s = ((1 + δ : ℝ) : ℂ) - t * Complex.I ∧
      s + 1 = ((1 - δ : ℝ) : ℂ) + t * Complex.I := by
    constructor <;> simp [s] <;> ring
  rcases hargs with ⟨hnum, hden⟩
  have hdenNorm := gamma_norm_conj_eq (1 - δ) t
  have hshift :
      Complex.Gamma (((1 + δ : ℝ) : ℂ) - t * Complex.I) /
        Complex.Gamma (((1 - δ : ℝ) : ℂ) - t * Complex.I) =
      (((1 - δ : ℝ) : ℂ) - t * Complex.I) *
        (Complex.Gamma (((1 + δ : ℝ) : ℂ) - t * Complex.I) /
          Complex.Gamma (((2 - δ : ℝ) : ℂ) - t * Complex.I)) := by
    have hrec' := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
      (((1 - δ : ℝ) : ℂ) - t * Complex.I)
    calc
      _ = Complex.Gamma (((1 + δ : ℝ) : ℂ) - t * Complex.I) *
          (Complex.Gamma (((1 - δ : ℝ) : ℂ) - t * Complex.I))⁻¹ := by
            rw [div_eq_mul_inv]
      _ = Complex.Gamma (((1 + δ : ℝ) : ℂ) - t * Complex.I) *
          ((((1 - δ : ℝ) : ℂ) - t * Complex.I) *
            (Complex.Gamma ((((1 - δ : ℝ) : ℂ) - t * Complex.I) + 1))⁻¹) := by
              rw [hrec']
      _ = (((1 - δ : ℝ) : ℂ) - t * Complex.I) *
          (Complex.Gamma (((1 + δ : ℝ) : ℂ) - t * Complex.I) /
            Complex.Gamma (((2 - δ : ℝ) : ℂ) - t * Complex.I)) := by
              rw [div_eq_mul_inv]
              have harg :
                  (((1 - δ : ℝ) : ℂ) - t * Complex.I) + 1 =
                    ((2 - δ : ℝ) : ℂ) - t * Complex.I := by push_cast; ring
              rw [harg]
              ring
  have hratioPos :
      ‖Complex.Gamma (((1 + δ : ℝ) : ℂ) - t * Complex.I) /
          Complex.Gamma (((2 - δ : ℝ) : ℂ) - t * Complex.I)‖ ≤
        Real.Gamma (1 + δ) / Real.Gamma (2 - δ) := by
    have htmp := gamma_positive_ratio_le (1 + δ) (1 - 2 * δ) (-t)
      (by linarith) (by linarith)
    convert htmp using 1 <;> congr 1 <;> push_cast <;> ring
  have hnormS : ‖s‖ ≤ 2 + |t| := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = δ + |t| := by simp [s, abs_of_pos hδ]
      _ ≤ 2 + |t| := by linarith
  have hnormShift :
      ‖(((1 - δ : ℝ) : ℂ) - t * Complex.I)‖ ≤ 2 + |t| := by
    calc
      ‖(((1 - δ : ℝ) : ℂ) - t * Complex.I)‖ ≤
          |((((1 - δ : ℝ) : ℂ) - t * Complex.I).re)| +
            |((((1 - δ : ℝ) : ℂ) - t * Complex.I).im)| :=
              Complex.norm_le_abs_re_add_abs_im _
      _ = |1 - δ| + |t| := by simp
      _ ≤ 2 + |t| := by
        have hpos : 0 ≤ 1 - δ := by linarith
        rw [abs_of_nonneg hpos]
        linarith
  calc
    ‖Complex.Gamma ((1 - (-δ + t * Complex.I)) : ℂ) /
        Complex.Gamma ((-δ + t * Complex.I) : ℂ)‖ =
      ‖Complex.Gamma (1 - s) / Complex.Gamma s‖ := by simp [s]
    _ = ‖s‖ * ‖Complex.Gamma (1 - s) / Complex.Gamma (s + 1)‖ := by
      rw [hratio, norm_mul]
    _ = ‖s‖ * ‖Complex.Gamma (((1 + δ : ℝ) : ℂ) - t * Complex.I) /
          Complex.Gamma (((1 - δ : ℝ) : ℂ) + t * Complex.I)‖ := by
        congr 2 <;> rw [hnum, hden]
    _ = ‖s‖ * ‖Complex.Gamma (((1 + δ : ℝ) : ℂ) - t * Complex.I) /
          Complex.Gamma (((1 - δ : ℝ) : ℂ) - t * Complex.I)‖ := by
        rw [norm_div, hdenNorm, ← norm_div]
    _ = ‖s‖ *
          (‖(((1 - δ : ℝ) : ℂ) - t * Complex.I)‖ *
            ‖Complex.Gamma (((1 + δ : ℝ) : ℂ) - t * Complex.I) /
              Complex.Gamma (((2 - δ : ℝ) : ℂ) - t * Complex.I)‖) := by
        rw [hshift, norm_mul]
    _ ≤ (2 + |t|) * ((2 + |t|) *
          (Real.Gamma (1 + δ) / Real.Gamma (2 - δ))) := by
        apply mul_le_mul hnormS
        · exact mul_le_mul hnormShift hratioPos (by positivity) (by positivity)
        · positivity
        · positivity
    _ = (Real.Gamma (1 + δ) / Real.Gamma (2 - δ)) * (2 + |t|) ^ 2 := by ring

private theorem gamma_ne_zero_of_re_between {z : ℂ} (hlo : -1 < z.re)
    (hhi : z.re < 0) : Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  have hre : z.re = -(n : ℝ) := by
    have h := congrArg Complex.re hn
    simpa using h
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst n
    simp at hre
    linarith
  · have hncast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    linarith

def gammaCLeftConstant (δ : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-1 - 2 * δ) * (Real.Gamma (1 + δ) / Real.Gamma (2 - δ))

def gammaRLeftConstant (δ : ℝ) : ℝ :=
  Real.pi ^ (-1 / 2 - δ) *
    (Real.Gamma ((1 + δ) / 2) / Real.Gamma (1 - δ / 2))

theorem gammaCLeftConstant_pos (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    0 < gammaCLeftConstant δ := by
  unfold gammaCLeftConstant
  have hp : 0 < 2 * Real.pi := by positivity
  have h1 : 0 < Real.Gamma (1 + δ) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma (2 - δ) := Real.Gamma_pos_of_pos (by linarith)
  positivity

theorem gammaRLeftConstant_pos (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    0 < gammaRLeftConstant δ := by
  unfold gammaRLeftConstant
  have h1 : 0 < Real.Gamma ((1 + δ) / 2) :=
    Real.Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Real.Gamma (1 - δ / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  positivity

theorem gammaC_left_ratio_bound (δ t : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    ‖Complex.Gammaℂ (1 - ((-δ : ℂ) + t * Complex.I)) /
      Complex.Gammaℂ ((-δ : ℂ) + t * Complex.I)‖ ≤
      gammaCLeftConstant δ * (2 + |t|) ^ 2 := by
  let s : ℂ := (-δ : ℂ) + t * Complex.I
  let p : ℝ := 2 * Real.pi
  let pC : ℂ := (2 * Real.pi : ℂ)
  have hp : 0 < p := by positivity
  have hpC : pC = (p : ℂ) := by simp [pC, p]
  have hpr : pC ≠ 0 := by rw [hpC]; exact Complex.ofReal_ne_zero.mpr hp.ne'
  have hsre : s.re = -δ := by simp [s]
  have hslo : -1 < s.re := by rw [hsre]; linarith
  have hshi : s.re < 0 := by rw [hsre]; linarith
  have hΓs : Complex.Gamma s ≠ 0 := gamma_ne_zero_of_re_between hslo hshi
  have hpow : pC ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpr)
  have hden : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hpow) hΓs
  have hsplit : Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s =
      (pC ^ (-(1 - s)) / pC ^ (-s)) *
        (Complex.Gamma (1 - s) / Complex.Gamma s) := by
    rw [Complex.Gammaℂ_def, Complex.Gammaℂ_def]
    field_simp [hΓs, hpow, pC]
    ring
  have hnormPow (z : ℂ) : ‖pC ^ z‖ = p ^ z.re := by
    rw [hpC]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp) z
  have hpowRatio :
      ‖pC ^ (-(1 - s)) / pC ^ (-s)‖ = p ^ (-1 - 2 * δ) := by
    rw [norm_div, hnormPow, hnormPow]
    have hnum : (-(1 - s)).re = -1 - δ := by simp [s]; ring
    have hden' : (-s).re = δ := by simp [s]
    rw [hnum, hden', ← Real.rpow_sub hp]
    congr 1
    ring
  have hratio := gamma_negative_ratio_le δ t hδ hδ4
  have hgamma : ‖Complex.Gamma (1 - s) / Complex.Gamma s‖ ≤
      (Real.Gamma (1 + δ) / Real.Gamma (2 - δ)) * (2 + |t|) ^ 2 := by
    simpa [s] using hratio
  calc
    ‖Complex.Gammaℂ (1 - ((-δ : ℂ) + t * Complex.I)) /
        Complex.Gammaℂ ((-δ : ℂ) + t * Complex.I)‖ =
      ‖Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s‖ := by simp [s]
    _ =
        ‖pC ^ (-(1 - s)) / pC ^ (-s)‖ *
          ‖Complex.Gamma (1 - s) / Complex.Gamma s‖ := by rw [hsplit, norm_mul]
    _ ≤ p ^ (-1 - 2 * δ) *
          ((Real.Gamma (1 + δ) / Real.Gamma (2 - δ)) * (2 + |t|) ^ 2) :=
        mul_le_mul hpowRatio.le hgamma (norm_nonneg _) (by positivity)
    _ = gammaCLeftConstant δ * (2 + |t|) ^ 2 := by simp [gammaCLeftConstant, p]; ring

theorem gammaR_left_ratio_bound (δ t : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    ‖Complex.Gammaℝ (1 - ((-δ : ℂ) + t * Complex.I)) /
      Complex.Gammaℝ ((-δ : ℂ) + t * Complex.I)‖ ≤
      gammaRLeftConstant δ * (2 + |t|) := by
  let s : ℂ := (-δ : ℂ) + t * Complex.I
  let p : ℝ := Real.pi
  let pC : ℂ := (Real.pi : ℂ)
  have hp : 0 < p := Real.pi_pos
  have hpC : pC = (p : ℂ) := by simp [pC, p]
  have hpr : pC ≠ 0 := by rw [hpC]; exact Complex.ofReal_ne_zero.mpr hp.ne'
  have hsre : s.re = -δ := by simp [s]
  have hs2lo : -1 < (s / 2).re := by simp [hsre]; linarith
  have hs2hi : (s / 2).re < 0 := by simp [hsre]; linarith
  have hΓs : Complex.Gamma (s / 2) ≠ 0 :=
    gamma_ne_zero_of_re_between hs2lo hs2hi
  have hpow : pC ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpr)
  have hden : Complex.Gammaℝ s ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    exact mul_ne_zero hpow hΓs
  have hsplit : Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s =
      (pC ^ (-(1 - s) / 2) / pC ^ (-s / 2)) *
        (Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2)) := by
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
    field_simp [hΓs, hpow, pC]
    ring
  have hnormPow (z : ℂ) : ‖pC ^ z‖ = p ^ z.re := by
    rw [hpC]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp) z
  have hpowRatio :
      ‖pC ^ (-(1 - s) / 2) / pC ^ (-s / 2)‖ = p ^ (-1 / 2 - δ) := by
    rw [norm_div, hnormPow, hnormPow]
    have hnum : (-(1 - s) / 2).re = -1 / 2 - δ / 2 := by simp [s]; ring
    have hden' : (-s / 2).re = δ / 2 := by simp [s]
    rw [hnum, hden', ← Real.rpow_sub hp]
    congr 1
    ring
  have hrec := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s / 2)
  have hratio : Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2) =
      (s / 2) * (Complex.Gamma ((1 - s) / 2) /
        Complex.Gamma (s / 2 + 1)) := by
    calc
      _ = Complex.Gamma ((1 - s) / 2) * (Complex.Gamma (s / 2))⁻¹ := by
        rw [div_eq_mul_inv]
      _ = Complex.Gamma ((1 - s) / 2) * ((s / 2) * (Complex.Gamma (s / 2 + 1))⁻¹) := by
        rw [hrec]
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hnumArg : (1 - s) / 2 = (((1 + δ) / 2 : ℝ) : ℂ) - (t / 2) * Complex.I := by
    simp [s]
    ring
  have hdenArg : s / 2 + 1 = (((1 - δ / 2 : ℝ) : ℂ) + (t / 2) * Complex.I) := by
    simp [s]
    ring
  have hdenNorm := gamma_norm_conj_eq (1 - δ / 2) (t / 2)
  have hdenNorm' :
      ‖Complex.Gamma (((1 - δ / 2 : ℝ) : ℂ) + ((t : ℝ) : ℂ) / 2 * Complex.I)‖ =
        ‖Complex.Gamma (((1 - δ / 2 : ℝ) : ℂ) - ((t : ℝ) : ℂ) / 2 * Complex.I)‖ := by
    simpa [Complex.ofReal_div] using hdenNorm
  have hratioPos :
      ‖Complex.Gamma ((((1 + δ) / 2 : ℝ) : ℂ) - (t / 2) * Complex.I) /
          Complex.Gamma (((1 - δ / 2 : ℝ) : ℂ) - (t / 2) * Complex.I)‖ ≤
        Real.Gamma ((1 + δ) / 2) / Real.Gamma (1 - δ / 2) := by
    have htmp := gamma_positive_ratio_le ((1 + δ) / 2) (1 / 2 - δ) (-t / 2)
      (by positivity) (by linarith)
    convert htmp using 1 <;> congr 1 <;> push_cast <;> ring
  have hnormS : ‖s‖ ≤ 2 + |t| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = δ + |t| := by simp [s, abs_of_pos hδ]
      _ ≤ 2 + |t| := by linarith
  have hnormHalf : ‖s / 2‖ ≤ 2 + |t| := by
    calc
      ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div]; norm_num
      _ ≤ ‖s‖ := by nlinarith [norm_nonneg s]
      _ ≤ 2 + |t| := hnormS
  have hgamma : ‖Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2)‖ ≤
      (Real.Gamma ((1 + δ) / 2) / Real.Gamma (1 - δ / 2)) * (2 + |t|) := by
    have hdenPos : 0 < Real.Gamma (1 - δ / 2) := by
      apply Real.Gamma_pos_of_pos
      linarith
    calc
      ‖Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2)‖ =
          ‖s / 2‖ * ‖Complex.Gamma ((1 - s) / 2) /
            Complex.Gamma (s / 2 + 1)‖ := by rw [hratio, norm_mul]
      _ = ‖s / 2‖ * ‖Complex.Gamma ((((1 + δ) / 2 : ℝ) : ℂ) - (t / 2) * Complex.I) /
            Complex.Gamma (((1 - δ / 2 : ℝ) : ℂ) + (t / 2) * Complex.I)‖ := by
              congr 2 <;> rw [hnumArg, hdenArg]
      _ = ‖s / 2‖ * ‖Complex.Gamma ((((1 + δ) / 2 : ℝ) : ℂ) - (t / 2) * Complex.I) /
            Complex.Gamma (((1 - δ / 2 : ℝ) : ℂ) - (t / 2) * Complex.I)‖ := by
              simp only [norm_div]
              rw [hdenNorm']
      _ ≤ (2 + |t|) *
            (Real.Gamma ((1 + δ) / 2) / Real.Gamma (1 - δ / 2)) := by
              exact mul_le_mul hnormHalf hratioPos (norm_nonneg _) (by positivity)
      _ = (Real.Gamma ((1 + δ) / 2) / Real.Gamma (1 - δ / 2)) * (2 + |t|) := by ring
  calc
    ‖Complex.Gammaℝ (1 - ((-δ : ℂ) + t * Complex.I)) /
        Complex.Gammaℝ ((-δ : ℂ) + t * Complex.I)‖ =
        ‖Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s‖ := by simp [s]
    _ = ‖pC ^ (-(1 - s) / 2) / pC ^ (-s / 2)‖ *
          ‖Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2)‖ := by
            rw [hsplit, norm_mul]
    _ ≤ p ^ (-1 / 2 - δ) *
          ((Real.Gamma ((1 + δ) / 2) / Real.Gamma (1 - δ / 2)) * (2 + |t|)) :=
        mul_le_mul hpowRatio.le hgamma (norm_nonneg _) (by positivity)
    _ = gammaRLeftConstant δ * (2 + |t|) := by simp [gammaRLeftConstant, p]; ring

end ArtinPrimitiveRoots.Proofs.HK_ANALYTIC
