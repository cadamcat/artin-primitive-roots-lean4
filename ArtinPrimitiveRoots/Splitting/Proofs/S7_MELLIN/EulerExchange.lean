import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».LineIntegrability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

universe u

open scoped NumberField BigOperators Topology
open NumberField IsDedekindDomain Filter MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting

/-- Absolute Euler norm summability exchanges the prime-power sum and the vertical integral. -/
theorem mellin_euler_exchange (M : ℂ → ℂ)
    (hentire : Differentiable ℂ M)
    (hdecay : ∀ (A : ℕ) (a b : ℝ), a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖M s‖ ≤ C * Real.rpow (1 + |s.im|) (-(A : ℝ)))
    (K : Type u) [Field K] [NumberField K]
    (hcoef : Summable (fun w : HeightOneSpectrum (𝓞 K) × ℕ =>
      Real.log (Ideal.absNorm w.1.asIdeal : ℝ) *
        Real.rpow (Ideal.absNorm w.1.asIdeal : ℝ) (-((w.2 + 1 : ℕ) : ℝ) * 2)))
    (x : ℝ) (hx : 0 < x) :
    Summable (fun w : HeightOneSpectrum (𝓞 K) × ℕ =>
      verticalLineIntegral (fun s : ℂ =>
        (Real.log (Ideal.absNorm w.1.asIdeal : ℝ) : ℂ) *
          (Ideal.absNorm w.1.asIdeal : ℂ) ^ (-((w.2 + 1 : ℕ) : ℂ) * s) *
          Complex.cpow (x : ℂ) s * M s) 2) ∧
    verticalLineIntegral (fun s : ℂ =>
      dedekindZetaLogDerivative K s * Complex.cpow (x : ℂ) s * M s) 2 =
      ∑' w : HeightOneSpectrum (𝓞 K) × ℕ,
        verticalLineIntegral (fun s : ℂ =>
          (Real.log (Ideal.absNorm w.1.asIdeal : ℝ) : ℂ) *
            (Ideal.absNorm w.1.asIdeal : ℂ) ^ (-((w.2 + 1 : ℕ) : ℂ) * s) *
            Complex.cpow (x : ℂ) s * M s) 2 := by
  let c : HeightOneSpectrum (𝓞 K) × ℕ → ℝ := fun w =>
    Real.log (Ideal.absNorm w.1.asIdeal : ℝ) *
      Real.rpow (Ideal.absNorm w.1.asIdeal : ℝ) (-((w.2 + 1 : ℕ) : ℝ) * 2)
  have hcSum : Summable c := hcoef
  have hN (v : HeightOneSpectrum (𝓞 K)) : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hNpos (v : HeightOneSpectrum (𝓞 K)) : 0 < Ideal.absNorm v.asIdeal :=
    lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hcpos (w : HeightOneSpectrum (𝓞 K) × ℕ) : 0 < c w :=
    mul_pos (Real.log_pos (hN w.1))
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one (hN w.1)) _)
  have hsupport : Function.support c = Set.univ := by
    ext w
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hcpos w).ne'
  letI : Countable (HeightOneSpectrum (𝓞 K) × ℕ) :=
    Set.countable_univ_iff.mp (by simpa only [hsupport] using hcSum.countable_support)
  let z : ℝ → ℂ := fun t => (2 : ℂ) + t * Complex.I
  let G : HeightOneSpectrum (𝓞 K) × ℕ → ℝ → ℂ := fun w t =>
    (Real.log (Ideal.absNorm w.1.asIdeal : ℝ) : ℂ) *
      (Ideal.absNorm w.1.asIdeal : ℂ) ^ (-((w.2 + 1 : ℕ) : ℂ) * z t)
  let F : HeightOneSpectrum (𝓞 K) × ℕ → ℝ → ℂ := fun w t =>
    G w t * Complex.cpow (x : ℂ) (z t) * M (z t)
  have hz : Continuous z := by dsimp only [z]; fun_prop
  have hzre (t : ℝ) : (z t).re = 2 := by simp [z]
  have hnormPow (w : HeightOneSpectrum (𝓞 K) × ℕ) (t : ℝ) :
      ‖(Ideal.absNorm w.1.asIdeal : ℂ) ^ (-((w.2 + 1 : ℕ) : ℂ) * z t)‖ =
        Real.rpow (Ideal.absNorm w.1.asIdeal : ℝ) (-((w.2 + 1 : ℕ) : ℝ) * 2) := by
    rw [Complex.norm_natCast_cpow_of_pos (hNpos w.1)]
    simp only [Complex.mul_re, Complex.neg_re, Complex.natCast_re, Complex.neg_im,
      Complex.natCast_im, neg_zero, zero_mul, sub_zero, hzre, Real.rpow_eq_pow]
  have hnormG (w : HeightOneSpectrum (𝓞 K) × ℕ) (t : ℝ) : ‖G w t‖ = c w := by
    simp only [G, c, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (hN w.1)), hnormPow]
  have hnormx (t : ℝ) : ‖Complex.cpow (x : ℂ) (z t)‖ = x ^ 2 := by
    rw [Complex.cpow_eq_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx, hzre,
      Real.rpow_two]
  have hnormF (w : HeightOneSpectrum (𝓞 K) × ℕ) (t : ℝ) :
      ‖F w t‖ = c w * x ^ 2 * ‖M (z t)‖ := by
    simp only [F, norm_mul, hnormG, hnormx]
  have hgSum (t : ℝ) : Summable (fun w => G w t) :=
    hcSum.of_norm_bounded fun w => (hnormG w t).le
  have hFCont (w : HeightOneSpectrum (𝓞 K) × ℕ) : Continuous (F w) := by
    have hprime : Continuous (fun t : ℝ =>
        (Ideal.absNorm w.1.asIdeal : ℂ) ^ (-((w.2 + 1 : ℕ) : ℂ) * z t)) :=
      (continuous_const.mul hz).const_cpow
        (.inl (Nat.cast_ne_zero.mpr (hNpos w.1).ne'))
    have hxpow : Continuous (fun t : ℝ => Complex.cpow (x : ℂ) (z t)) := by
      simpa only [Complex.cpow_eq_pow] using
        hz.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    exact ((continuous_const.mul hprime).mul hxpow).mul (hentire.continuous.comp hz)
  have hM : Integrable (fun t : ℝ => M (z t)) := by
    obtain ⟨C, hC, hbound⟩ := hdecay 6 2 2 (by norm_num)
    have hPhi : Continuous (fun t : ℝ => M (z t)) := hentire.continuous.comp hz
    have hgrowth (t : ℝ) : ‖(1 : ℂ)‖ ≤
        1 * Real.rpow (1 + |t|) (4 : ℝ) := by
      simp only [norm_one, one_mul, Real.rpow_eq_pow]
      exact Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
    have hdec (t : ℝ) : ‖M (z t)‖ ≤ C * Real.rpow (1 + |t|) (-6 : ℝ) := by
      simpa [z] using hbound (z t) (by rw [hzre]) (by rw [hzre])
    have h := integrable_product_of_growth_decay (fun _ : ℝ => (1 : ℂ))
      (fun t : ℝ => M (z t)) aestronglyMeasurable_const hPhi.aestronglyMeasurable
      1 C (by norm_num) hC.le hgrowth hdec
    simpa only [one_mul] using h
  have hFint (w : HeightOneSpectrum (𝓞 K) × ℕ) : Integrable (F w) :=
    (hM.norm.const_mul (c w * x ^ 2)).mono' (hFCont w).aestronglyMeasurable
      (Eventually.of_forall fun t => (hnormF w t).le)
  have hnormInt (w : HeightOneSpectrum (𝓞 K) × ℕ) :
      (∫ t : ℝ, ‖F w t‖) = c w * x ^ 2 * ∫ t : ℝ, ‖M (z t)‖ := by
    calc
      _ = ∫ t : ℝ, c w * x ^ 2 * ‖M (z t)‖ :=
        integral_congr_ae (Eventually.of_forall fun t => hnormF w t)
      _ = _ := integral_const_mul _ _
  have hnormInts : Summable (fun w => ∫ t : ℝ, ‖F w t‖) := by
    refine ((hcSum.mul_right (x ^ 2)).mul_right (∫ t : ℝ, ‖M (z t)‖)).congr ?_
    intro w
    exact (hnormInt w).symm
  have hseries (t : ℝ) : (∑' w, F w t) =
      dedekindZetaLogDerivative K (z t) * Complex.cpow (x : ℂ) (z t) * M (z t) := by
    have hEuler := ArtinPrimitiveRoots.Ext.SplittingInputs.ext_dedekind_euler_logderiv K
      (s := z t) (by rw [hzre]; norm_num)
    calc
      _ = (∑' w, G w t) * (Complex.cpow (x : ℂ) (z t) * M (z t)) := by
        rw [← (hgSum t).tsum_mul_right (Complex.cpow (x : ℂ) (z t) * M (z t))]
        exact tsum_congr fun w => mul_assoc _ _ _
      _ = _ := by
        rw [(hgSum t).tsum_prod, ← hEuler.2.2]
        exact (mul_assoc _ _ _).symm
  have hInt := hasSum_integral_of_summable_integral_norm hFint hnormInts
  have hNormalized := hInt.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  refine ⟨?_, ?_⟩
  · simpa only [verticalLineIntegral, z, F, G, Complex.ofReal_ofNat] using hNormalized.summable
  · have hident : (∫ t : ℝ, ∑' w, F w t) =
        ∫ t : ℝ, dedekindZetaLogDerivative K (z t) *
          Complex.cpow (x : ℂ) (z t) * M (z t) :=
      integral_congr_ae (Eventually.of_forall hseries)
    have hEq := hNormalized.tsum_eq
    rw [hident] at hEq
    simpa only [verticalLineIntegral, z, F, G, Complex.ofReal_ofNat] using hEq.symm

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
