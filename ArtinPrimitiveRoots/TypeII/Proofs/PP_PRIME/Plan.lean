import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Marked
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.PP_PRIME

open Classical
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP
open MeasureTheory
open scoped FourierTransform

noncomputable def mangoldtIntervalPolynomial (N : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (I : Set ℕ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter
      (fun n : ℕ => 1 ≤ n ∧ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N ∧ n ∈ I),
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) *
      Complex.exp ((-1 + Complex.I * t) * Real.log (n : ℝ))

noncomputable def smoothedMangoldtPolynomial (N : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (g : ℝ → ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊3 * N⌋₊ + 1)).filter (fun n : ℕ => 1 ≤ n),
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) *
      Complex.exp ((-1 + Complex.I * t) * Real.log (n : ℝ)) *
        (g ((n : ℝ) / N) : ℂ)

noncomputable def mellinKernel (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ w : ℝ in Set.Ioi 0,
    (g w : ℂ) * Complex.exp (z * Real.log w) / (w : ℂ)

noncomputable def mellinLogWeight (g : ℝ → ℝ) (α u : ℝ) : ℂ :=
  (Real.exp (-α * u) : ℂ) * (g (Real.exp (-u)) : ℂ)

/-- The kernel is Mathlib's Mellin transform, with the positive-base power
rewritten only on the domain of integration. -/
theorem mellinKernel_eq_mellin (g : ℝ → ℝ) (z : ℂ) :
    mellinKernel g z = mellin (fun w : ℝ => (g w : ℂ)) z := by
  unfold mellinKernel mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [smul_eq_mul]
  have hwpos : 0 < w := hw
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hwpos.ne'
  have hlog : Complex.log (w : ℂ) = (Real.log w : ℂ) :=
    (Complex.ofReal_log hwpos.le).symm
  rw [Complex.cpow_def_of_ne_zero hwC, hlog]
  have hexp : Complex.exp (Real.log w : ℂ) = (w : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hwpos]
  calc
    (g w : ℂ) * Complex.exp (z * (Real.log w : ℂ)) / (w : ℂ) =
        (Complex.exp (z * (Real.log w : ℂ)) / (w : ℂ)) * (g w : ℂ) := by ring
    _ = Complex.exp ((z - 1) * (Real.log w : ℂ)) * (g w : ℂ) := by
      rw [← hexp, ← Complex.exp_sub]
      congr 1
      ring
    _ = Complex.exp ((Real.log w : ℂ) * (z - 1)) * (g w : ℂ) := by
      congr 2
      ring

private theorem ppPrime_fourier_norm_le_integral_norm (f : ℝ → ℂ)
    (_hf : Integrable f) (w : ℝ) : ‖𝓕 f w‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) f w

private theorem ppPrime_fourier_polynomial_decay (f : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hderiv : ∀ n : ℕ, Integrable (iteratedDeriv n f))
    (j : ℕ) (A₀ Aⱼ : ℝ) (hA₀ : 0 ≤ A₀)
    (hbound₀ : ∫ u : ℝ, ‖f u‖ ≤ A₀)
    (hboundⱼ : ∫ u : ℝ, ‖iteratedDeriv j f u‖ ≤ Aⱼ) :
    ∀ w : ℝ, ‖𝓕 f w‖ ≤ max (A₀ * 2 ^ j) Aⱼ / (1 + |w|) ^ j := by
  have hfreqFun : 𝓕 (iteratedDeriv j f) = fun w : ℝ =>
      (2 * Real.pi * Complex.I * (w : ℂ)) ^ j • 𝓕 f w := by
    simpa [smul_eq_mul] using
      (Real.fourier_iteratedDeriv (N := ⊤) hf (fun n _ => hderiv n) (by simp))
  have hfreq (w : ℝ) : 𝓕 (iteratedDeriv j f) w =
      (2 * Real.pi * Complex.I * (w : ℂ)) ^ j * 𝓕 f w := by
    simpa [smul_eq_mul] using congrFun hfreqFun w
  have hqnorm (w : ℝ) :
      ‖(2 * Real.pi * Complex.I * (w : ℂ))‖ = 2 * Real.pi * |w| := by
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hI : ‖Complex.I‖ = 1 := by simp
    have hwR : ‖(w : ℂ)‖ = |w| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      _ = ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖Complex.I‖ * ‖(w : ℂ)‖ := by
        simp only [norm_mul]
      _ = 2 * Real.pi * |w| := by rw [htwo, hpi, hI, hwR]; ring
  intro w
  let Aₙ : ℝ := ∫ u : ℝ, ‖iteratedDeriv j f u‖
  have hFourier₀ := ppPrime_fourier_norm_le_integral_norm f (hderiv 0) w
  have hFourier₀' : ‖𝓕 f w‖ ≤ A₀ := by simpa [iteratedDeriv_zero] using hFourier₀.trans hbound₀
  have hden : 0 < (1 + |w|) ^ j := pow_pos (by positivity) _
  rcases le_total |w| 1 with hw | hw
  · apply (le_div_iff₀ hden).2
    have hdenLe : (1 + |w|) ^ j ≤ (2 : ℝ) ^ j :=
      pow_le_pow_left₀ (by positivity) (by linarith) j
    calc
      ‖𝓕 f w‖ * (1 + |w|) ^ j ≤ A₀ * (1 + |w|) ^ j :=
        mul_le_mul_of_nonneg_right hFourier₀' (by positivity)
      _ ≤ A₀ * 2 ^ j := mul_le_mul_of_nonneg_left hdenLe hA₀
      _ ≤ max (A₀ * 2 ^ j) Aⱼ := le_max_left _ _
  · have hqpos : 0 < 2 * Real.pi * |w| := by positivity
    have hqge : 1 + |w| ≤ 2 * Real.pi * |w| := by
      nlinarith [Real.pi_gt_three, abs_nonneg w, hw]
    have hqpow : (1 + |w|) ^ j ≤ (2 * Real.pi * |w|) ^ j :=
      pow_le_pow_left₀ (by positivity) hqge j
    have hFourierN := ppPrime_fourier_norm_le_integral_norm
      (iteratedDeriv j f) (hderiv j) w
    have hFourierN' : ‖𝓕 (iteratedDeriv j f) w‖ ≤ Aⱼ := by
      exact hFourierN.trans (by simpa [Aₙ] using hboundⱼ)
    have hnormN : ‖𝓕 (iteratedDeriv j f) w‖ =
        (2 * Real.pi * |w|) ^ j * ‖𝓕 f w‖ := by
      rw [hfreq w, norm_mul, norm_pow, hqnorm]
    have hprod : ‖𝓕 f w‖ * (1 + |w|) ^ j ≤ Aⱼ := by
      calc
        _ ≤ ‖𝓕 f w‖ * (2 * Real.pi * |w|) ^ j :=
          mul_le_mul_of_nonneg_left hqpow (norm_nonneg _)
        _ = ‖𝓕 (iteratedDeriv j f) w‖ := by rw [hnormN]; ring
        _ ≤ Aⱼ := hFourierN'
    apply (le_div_iff₀ hden).2
    calc
      ‖𝓕 f w‖ * (1 + |w|) ^ j ≤ Aⱼ := hprod
      _ ≤ max (A₀ * 2 ^ j) Aⱼ := le_max_right _ _

/-- Compact support and derivative control give a uniform vertical Mellin bound. -/
theorem mellinKernel_uniform_decay (g : ℝ → ℝ) (L A : ℝ)
    (hL : 1 ≤ L) (hA : 0 < A) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hsmooth : ∀ α, |α| ≤ 1 →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mellinLogWeight g α))
    (hint : ∀ α, |α| ≤ 1 → ∀ j,
      Integrable (iteratedDeriv j (mellinLogWeight g α)))
    (hbound : ∀ α, |α| ≤ 1 → ∀ j,
      ∫ u : ℝ, ‖iteratedDeriv j (mellinLogWeight g α) u‖ ≤
        K j * Real.rpow L ((j : ℝ) * (A + 4))) :
    ∀ j : ℕ, ∃ Mj : ℝ, 0 < Mj ∧
      ∀ α v : ℝ, |α| ≤ 1 →
        ‖mellinKernel g (⟨α, v⟩ : ℂ)‖ ≤
          Mj * Real.rpow L (((j + 1 : ℕ) : ℝ) * (A + 5)) *
            Real.rpow (1 + |v|) (-(j : ℝ)) := by
  classical
  intro j
  let E : ℝ := ((j + 1 : ℕ) : ℝ) * (A + 5)
  let Mj : ℝ := (2 * Real.pi) ^ j * (K 0 * 2 ^ j + K j) + 1
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hExponent : (j : ℝ) * (A + 4) ≤ E := by
    dsimp [E]
    push_cast
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    nlinarith [hA]
  have hLp : Real.rpow L ((j : ℝ) * (A + 4)) ≤ Real.rpow L E :=
    Real.rpow_le_rpow_of_exponent_le hL hExponent
  have hLE : 1 ≤ Real.rpow L E := Real.one_le_rpow hL hE
  have hK0 : 0 ≤ K 0 := hK 0
  have hKj : 0 ≤ K j := hK j
  have hL0 : 0 ≤ L := le_trans (by norm_num : (0 : ℝ) ≤ 1) hL
  have hMj : 0 < Mj := by dsimp [Mj]; positivity
  refine ⟨Mj, hMj, ?_⟩
  intro α v hα
  let f : ℝ → ℂ := mellinLogWeight g α
  have hline : mellinKernel g (⟨α, v⟩ : ℂ) = 𝓕 f (v / (2 * Real.pi)) := by
    rw [mellinKernel_eq_mellin, mellin_eq_fourier]
    have hfun : (fun u : ℝ =>
        Real.exp (-((⟨α, v⟩ : ℂ).re) * u) • (g (Real.exp (-u)) : ℂ)) = f := by
      funext u
      simp [f, mellinLogWeight, Complex.ofReal_exp]
    rw [hfun]
  have hA0 : ∫ u : ℝ, ‖f u‖ ≤ K 0 := by
    have h := hbound α hα 0
    simpa [f, mellinLogWeight, iteratedDeriv_zero, Real.rpow_zero] using h
  have hAj : ∫ u : ℝ, ‖iteratedDeriv j f u‖ ≤
      K j * Real.rpow L ((j : ℝ) * (A + 4)) := by
    exact hbound α hα j
  have hdec := ppPrime_fourier_polynomial_decay f (hsmooth α hα)
    (hint α hα) j (K 0) (K j * Real.rpow L ((j : ℝ) * (A + 4)))
    hK0 hA0 hAj
  let w : ℝ := v / (2 * Real.pi)
  have hv : v = (2 * Real.pi) * w := by
    dsimp [w]
    field_simp
  have habs : |v| = 2 * Real.pi * |w| := by
    rw [hv, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hscale : 1 + |v| ≤ (2 * Real.pi) * (1 + |w|) := by
    rw [habs]
    have hq : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [abs_nonneg w]
  have hscalePow : (1 + |v|) ^ j ≤ (2 * Real.pi) ^ j * (1 + |w|) ^ j := by
    calc
      (1 + |v|) ^ j ≤ ((2 * Real.pi) * (1 + |w|)) ^ j :=
        pow_le_pow_left₀ (by positivity) hscale j
      _ = (2 * Real.pi) ^ j * (1 + |w|) ^ j := by rw [mul_pow]
  have hdenw : 0 < (1 + |w|) ^ j := pow_pos (by positivity) _
  have hdenv : 0 < (1 + |v|) ^ j := pow_pos (by positivity) _
  have hLepos : 0 ≤ Real.rpow L E := le_trans (by norm_num) hLE
  have hTerm0 : 0 ≤ K 0 * 2 ^ j := mul_nonneg hK0 (by positivity)
  have hMax : max (K 0 * 2 ^ j) (K j * Real.rpow L ((j : ℝ) * (A + 4))) ≤
      (K 0 * 2 ^ j + K j) * Real.rpow L E := by
    apply max_le
    · calc
        K 0 * 2 ^ j = (K 0 * 2 ^ j) * 1 := by ring
        _ ≤ (K 0 * 2 ^ j) * Real.rpow L E :=
          mul_le_mul_of_nonneg_left hLE hTerm0
        _ ≤ (K 0 * 2 ^ j + K j) * Real.rpow L E :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hKj) hLepos
    · calc
        K j * Real.rpow L ((j : ℝ) * (A + 4)) ≤ K j * Real.rpow L E :=
          mul_le_mul_of_nonneg_left hLp hKj
        _ ≤ (K 0 * 2 ^ j + K j) * Real.rpow L E :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hTerm0) hLepos
  have hdecLine : ‖𝓕 f w‖ ≤
      max (K 0 * 2 ^ j) (K j * Real.rpow L ((j : ℝ) * (A + 4))) /
        (1 + |w|) ^ j := by
    exact hdec w
  have hratio : 1 / (1 + |w|) ^ j ≤ (2 * Real.pi) ^ j / (1 + |v|) ^ j := by
    apply (div_le_div_iff₀ hdenw hdenv).2
    simpa only [one_mul] using hscalePow
  have hFourier : ‖𝓕 f w‖ ≤
      (K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j * Real.rpow L E /
        (1 + |v|) ^ j := by
    calc
      ‖𝓕 f w‖ ≤
          max (K 0 * 2 ^ j) (K j * Real.rpow L ((j : ℝ) * (A + 4))) /
            (1 + |w|) ^ j := hdecLine
      _ ≤ ((K 0 * 2 ^ j + K j) * Real.rpow L E) /
            (1 + |w|) ^ j :=
        div_le_div_of_nonneg_right hMax (by positivity)
      _ = (K 0 * 2 ^ j + K j) * Real.rpow L E *
            (1 / (1 + |w|) ^ j) := by rw [div_eq_mul_inv, one_div]
      _ ≤ (K 0 * 2 ^ j + K j) * Real.rpow L E *
            ((2 * Real.pi) ^ j / (1 + |v|) ^ j) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j * Real.rpow L E /
            (1 + |v|) ^ j := by ring
  have hC : (K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j ≤ Mj := by
    dsimp [Mj]
    nlinarith [mul_nonneg (add_nonneg (mul_nonneg hK0 (by positivity)) hKj)
      (by positivity : 0 ≤ (2 * Real.pi) ^ j)]
  have hFinal : ‖mellinKernel g (⟨α, v⟩ : ℂ)‖ ≤
      Mj * Real.rpow L E / (1 + |v|) ^ j := by
    calc
      ‖mellinKernel g (⟨α, v⟩ : ℂ)‖ = ‖𝓕 f w‖ := by
        simpa [w] using congrArg norm hline
      _ ≤ (K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j * Real.rpow L E /
            (1 + |v|) ^ j := hFourier
      _ ≤ Mj * Real.rpow L E / (1 + |v|) ^ j := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc
          (K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j * Real.rpow L E =
              ((K 0 * 2 ^ j + K j) * (2 * Real.pi) ^ j) * Real.rpow L E := by ring
          _ ≤ Mj * Real.rpow L E := mul_le_mul_of_nonneg_right hC hLepos
  have hRpow : Real.rpow (1 + |v|) (-(j : ℝ)) = 1 / (1 + |v|) ^ j := by
    calc
      Real.rpow (1 + |v|) (-(j : ℝ)) =
          (Real.rpow (1 + |v|) (j : ℝ))⁻¹ :=
        Real.rpow_neg (by positivity) (j : ℝ)
      _ = ((1 + |v|) ^ j)⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast (1 + |v|) j)
      _ = 1 / (1 + |v|) ^ j := by simp [one_div]
  rw [hRpow]
  simpa [E, div_eq_mul_inv, mul_assoc] using hFinal

/-- Mellin inversion on a compactly supported smooth positive-coordinate weight. -/
theorem mellinKernel_inversion (g : ℝ → ℝ)
    (hg : ContDiff ℝ ⊤ g)
    (hsupport : Function.support g ⊆ Set.Icc (1 / 2 : ℝ) 3)
    (c w : ℝ) (hw : 0 < w) :
    (g w : ℂ) = (1 / (2 * Real.pi) : ℂ) *
      ∫ v : ℝ, mellinKernel g (⟨c, v⟩ : ℂ) *
        Complex.exp (-((⟨c, v⟩ : ℂ) * Real.log w)) := by
  classical
  let f : ℝ → ℂ := mellinLogWeight g c
  have hfsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => Real.exp (-c * u)) := by fun_prop
    have hBtop : ContDiff ℝ ⊤
        (fun u : ℝ => g (Real.exp (-u))) := by
      have harg : ContDiff ℝ ⊤
          (fun u : ℝ => Real.exp (-u)) := by fun_prop
      exact hg.comp harg
    have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => g (Real.exp (-u))) := hBtop.of_le le_top
    have hAc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => (Real.exp (-c * u) : ℂ)) := Complex.ofRealCLM.contDiff.comp hA
    have hBc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => (g (Real.exp (-u)) : ℂ)) := Complex.ofRealCLM.contDiff.comp hB
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => (Real.exp (-c * u) : ℂ) * (g (Real.exp (-u)) : ℂ))
    exact hAc.mul hBc
  have hfsupport : Function.support f ⊆ Set.Icc (-Real.log 3) (-Real.log (1 / 2)) := by
    intro u hu
    have hfu : f u ≠ 0 := by
      simpa only [Function.mem_support] using hu
    have hgu : g (Real.exp (-u)) ≠ 0 := by
      intro hz
      apply hfu
      simp [f, mellinLogWeight, hz]
    have hmem : Real.exp (-u) ∈ Function.support g := by
      simpa only [Function.mem_support] using hgu
    rcases hsupport hmem with ⟨hlo, hhi⟩
    constructor
    · have hlog := Real.log_le_log (Real.exp_pos (-u)) hhi
      have hlog' : -u ≤ Real.log 3 := by simpa only [Real.log_exp] using hlog
      linarith
    · have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hlo
      have hlog' : Real.log (1 / 2) ≤ -u := by simpa only [Real.log_exp] using hlog
      linarith
  have hfcompact : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hfsupport
  let F : SchwartzMap ℝ ℂ := hfcompact.toSchwartzMap hfsmooth
  have hFcoe : (F : ℝ → ℂ) = f := rfl
  have hline (v : ℝ) :
      mellinKernel g (⟨c, v⟩ : ℂ) = 𝓕 f (v / (2 * Real.pi)) := by
    rw [mellinKernel_eq_mellin, mellin_eq_fourier]
    have hfun : (fun u : ℝ =>
        Real.exp (-((⟨c, v⟩ : ℂ).re) * u) • (g (Real.exp (-u)) : ℂ)) = f := by
      funext u
      simp [f, mellinLogWeight, Complex.ofReal_exp]
    rw [hfun]
  have hFt : 𝓕 f = ((𝓕 F : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    rw [SchwartzMap.fourier_coe]
    rfl
  let x : ℝ := -Real.log w
  have hInv : 𝓕⁻ (𝓕 f) x = f x := by
    exact congrFun (F.continuous.fourierInv_fourier_eq F.integrable
      (𝓕 F).integrable) x
  have hInvIntegral : 𝓕⁻ (𝓕 f) x =
      ∫ y : ℝ, Complex.exp ((↑(2 * Real.pi * (y * x) : ℝ) : ℂ) * Complex.I) * 𝓕 f y := by
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply, smul_eq_mul]
  let H : ℝ → ℂ := fun v => mellinKernel g (⟨c, v⟩ : ℂ) *
    Complex.exp (Complex.I * (v : ℂ) * (x : ℂ))
  have hπ : 0 < 2 * Real.pi := by positivity
  have hchange : (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) •
      ∫ y : ℝ, H ((2 * Real.pi) * y) := by
    have h := Measure.integral_comp_mul_left H (2 * Real.pi)
    rw [abs_of_pos (inv_pos.mpr hπ)] at h
    calc
      (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) •
          ((2 * Real.pi : ℝ)⁻¹ • ∫ v : ℝ, H v) := by
            rw [smul_smul, mul_inv_cancel₀ hπ.ne', one_smul]
      _ = (2 * Real.pi : ℝ) • ∫ y : ℝ, H ((2 * Real.pi) * y) := by rw [h.symm]
  have hscaled (y : ℝ) :
      H ((2 * Real.pi) * y) =
        Complex.exp ((↑(2 * Real.pi * (y * x) : ℝ) : ℂ) * Complex.I) * 𝓕 f y := by
    dsimp [H]
    rw [hline]
    have hfreq : (2 * Real.pi * y) / (2 * Real.pi) = y := by
      field_simp [Real.pi_ne_zero]
    rw [hfreq]
    have hexp : Complex.I * (↑(2 * Real.pi * y : ℝ) : ℂ) * (x : ℂ) =
        (↑(2 * Real.pi * (y * x) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [congrArg Complex.exp hexp]
    ring
  have hscaledIntegral : (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, H v =
      ∫ y : ℝ, Complex.exp ((↑(2 * Real.pi * (y * x) : ℝ) : ℂ) * Complex.I) * 𝓕 f y := by
    rw [hchange]
    have hchange' : (2 * Real.pi : ℝ) • (∫ y : ℝ, H ((2 * Real.pi) * y)) =
        ((2 * Real.pi : ℝ) : ℂ) * ∫ y : ℝ, H ((2 * Real.pi) * y) := by
      rfl
    have hcoef : (1 / (2 * Real.pi) : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = 1 := by
      norm_cast
      field_simp [Real.pi_ne_zero]
    calc
      (1 / (2 * Real.pi) : ℂ) *
          ((2 * Real.pi : ℝ) • ∫ y : ℝ, H ((2 * Real.pi) * y)) =
          (1 / (2 * Real.pi) : ℂ) *
            (((2 * Real.pi : ℝ) : ℂ) * ∫ y : ℝ, H ((2 * Real.pi) * y)) := by rw [hchange']
      _ = ((1 / (2 * Real.pi) : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) *
          ∫ y : ℝ, H ((2 * Real.pi) * y) := by rw [mul_assoc]
      _ = ∫ y : ℝ, H ((2 * Real.pi) * y) := by rw [hcoef, one_mul]
      _ = ∫ y : ℝ, Complex.exp ((↑(2 * Real.pi * (y * x) : ℝ) : ℂ) * Complex.I) *
          𝓕 f y := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hscaled
  have hfAt : f x =
      (Real.exp (-c * x) : ℂ) * (g (Real.exp (-x)) : ℂ) := by
    rfl
  have htarget : (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, H v = f x := by
    rw [hscaledIntegral, ← hInvIntegral, hInv]
  have hlogw : Real.exp (-x) = w := by
    simp [x, Real.exp_log hw]
  have hfinal : f x * (Real.exp (-c * x) : ℂ)⁻¹ = (g w : ℂ) := by
    rw [hfAt, hlogw]
    have he : (Real.exp (-c * x) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
    field_simp
  calc
    (g w : ℂ) = f x * (Real.exp (-c * x) : ℂ)⁻¹ := hfinal.symm
    _ = ((1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, H v) *
        (Real.exp (-c * x) : ℂ)⁻¹ := by rw [htarget]
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ,
        mellinKernel g (⟨c, v⟩ : ℂ) *
          Complex.exp (-((⟨c, v⟩ : ℂ) * Real.log w)) := by
      have hE : (Real.exp (-c * x) : ℂ)⁻¹ =
        Complex.exp ((c : ℂ) * (x : ℂ)) := by
        rw [Complex.ofReal_exp]
        rw [← Complex.exp_neg]
        congr 1
        push_cast
        ring
      have hphase (v : ℝ) :
          Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
              Complex.exp ((c : ℂ) * (x : ℂ)) =
            Complex.exp (-((⟨c, v⟩ : ℂ) * (Real.log w : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        have hx : (x : ℂ) = -(Real.log w : ℂ) := by
          simp [x]
        rw [hx]
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      calc
        _ = (1 / (2 * Real.pi) : ℂ) *
            ((∫ v : ℝ, H v) * (Real.exp (-c * x) : ℂ)⁻¹) := by ring
        _ = (1 / (2 * Real.pi) : ℂ) *
            ∫ v : ℝ, H v * (Real.exp (-c * x) : ℂ)⁻¹ := by rw [integral_mul_const]
        _ = (1 / (2 * Real.pi) : ℂ) *
            ∫ v : ℝ, mellinKernel g (⟨c, v⟩ : ℂ) *
              Complex.exp (-((⟨c, v⟩ : ℂ) * (Real.log w : ℂ))) := by
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun v => by
            dsimp [H]
            rw [hE]
            calc
              mellinKernel g (⟨c, v⟩ : ℂ) *
                  Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
                    Complex.exp ((c : ℂ) * (x : ℂ)) =
                  mellinKernel g (⟨c, v⟩ : ℂ) *
                    (Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
                      Complex.exp ((c : ℂ) * (x : ℂ))) := by ring
              _ = mellinKernel g (⟨c, v⟩ : ℂ) *
                  Complex.exp (-((⟨c, v⟩ : ℂ) * (Real.log w : ℂ))) := by rw [hphase]

/-- The sharp von Mangoldt polynomial has uniform cancellation in every natural interval. -/
theorem prime_mangoldt_interval_bound :
    ∀ τ η C A : ℝ, 0 < τ → τ < η → η < 1 → 0 < C → 0 < A →
      ∃ B₀ K x₀ : ℝ, 0 < B₀ ∧ 0 < K ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ N : ℝ, Real.rpow x τ / 2 ≤ N → N ≤ Real.rpow x η →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
                Real.rpow L B₀ ≤ |t| → |t| ≤ Real.rpow x 2 →
                  ∀ I : Set ℕ, IsNatInterval I →
                    I ⊆ {n : ℕ | N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N} →
                      ‖mangoldtIntervalPolynomial N q χ t I‖ ≤
                        K * Real.rpow L (-A - 2) := by
  sorry

/-- The prime-power terms are a uniform lower-order error in a dyadic interval. -/
theorem prime_power_removal {N : ℝ} (hN : 4 ≤ N) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (I : Set ℕ)
    (hI : I ⊆ {n : ℕ | N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N}) :
    ‖mangoldtIntervalPolynomial N q χ t I -
      ∑ p ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N ∧ p ∈ I),
        (Real.log (p : ℝ) : ℂ) * χ (p : ZMod q) *
          Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ))‖ ≤
      100 * Real.rpow N (-1 / 2) * (Real.log (3 * N)) ^ 2 := by
  sorry

/-- Final interval Abel transfer and logarithm removal, to be assembled from the preceding bounds. -/
theorem prime_polynomial_core :
    ∀ τ η C A : ℝ, 0 < τ → τ < η → η < 1 → 0 < C → 0 < A →
      ∃ B₀ C₀ x₀ : ℝ, 0 < B₀ ∧ 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ N : ℝ, Real.rpow x τ / 2 ≤ N → N ≤ Real.rpow x η →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
                Real.rpow L B₀ ≤ |t| → |t| ≤ Real.rpow x 2 →
                  ∀ I : Set ℕ, IsNatInterval I →
                    I ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N} →
                      ‖primeDirichletPolynomial N q χ t I‖ ≤
                        C₀ * Real.rpow L (-A) := by
  sorry

end ArtinPrimitiveRoots.Proofs.PP_PRIME
