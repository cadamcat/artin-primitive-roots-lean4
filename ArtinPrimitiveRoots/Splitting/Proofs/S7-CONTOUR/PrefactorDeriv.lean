import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».GammaHorizontal
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».Continuation
import Mathlib.Analysis.Calculus.LogDeriv

set_option autoImplicit false

open NumberField

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke

/-- The discriminant and archimedean factors have the expected logarithmic derivative off the real axis. -/
theorem prefactor_logderiv (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ (dedekindPrefactor K) s ∧
    dedekindPrefactor K s ≠ 0 ∧
    deriv (dedekindPrefactor K) s / dedekindPrefactor K s =
      (Real.log (absoluteDiscriminant K) : ℂ) / 2 +
      (InfinitePlace.nrRealPlaces K : ℂ) *
        (-(Real.log Real.pi : ℂ) / 2 +
          (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2) +
      (InfinitePlace.nrComplexPlaces K : ℂ) *
        (-(Real.log (2 * Real.pi) : ℂ) +
          deriv Complex.Gamma s / Complex.Gamma s) := by
  let D : ℂ := (absoluteDiscriminant K : ℂ)
  have hDreal : 0 < absoluteDiscriminant K := by
    exact abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast hDreal.ne'
  have hDlog : Complex.log D = (Real.log (absoluteDiscriminant K) : ℂ) :=
    (Complex.ofReal_log hDreal.le).symm
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpi₂ : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hpi
  have hlogpi : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  have hlogpi₂ : Complex.log (2 * (Real.pi : ℂ)) = (Real.log (2 * Real.pi) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      (Complex.ofReal_log (show 0 ≤ 2 * Real.pi by positivity)).symm
  have hhalfim : (s / 2).im ≠ 0 := by
    rw [Complex.div_ofNat_im]
    exact div_ne_zero hs (by norm_num)
  have hpole (z : ℂ) (hz : z.im ≠ 0) (m : ℕ) : z ≠ -(m : ℂ) := by
    intro h
    apply hz
    simp [h]
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (hpole s hs)
  have hGhalf : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero (hpole (s / 2) hhalfim)
  have hdG : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s (hpole s hs)
  have hdGhalf : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma (s / 2) (hpole (s / 2) hhalfim)
  have hhalf : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const (2 : ℂ)
  have hneg : HasDerivAt (fun z : ℂ => -z) (-1) s := by
    exact (hasDerivAt_id s).neg
  have hneghalf : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) s := by
    simpa using ((hasDerivAt_id s).neg).div_const (2 : ℂ)
  have hdD : DifferentiableAt ℂ (fun z : ℂ => D ^ (z / 2)) s :=
    hhalf.differentiableAt.const_cpow (Or.inl hD)
  have hdRpow : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    hneghalf.differentiableAt.const_cpow (Or.inl hpi)
  have hdCpow : DifferentiableAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    hneg.differentiableAt.const_cpow (Or.inl hpi₂)
  have hdGcomp : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    hdGhalf.comp s hhalf.differentiableAt
  have hDpow : D ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hD)
  have hRpow : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hCpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi₂)
  have hR : Complex.Gammaℝ s ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    exact mul_ne_zero hRpow hGhalf
  have hC : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hCpow) hG
  have hdR : DifferentiableAt ℂ Complex.Gammaℝ s := by
    change DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) *
      Complex.Gamma (z / 2)) s
    exact hdRpow.mul hdGcomp
  have hdC : DifferentiableAt ℂ Complex.Gammaℂ s := by
    change DifferentiableAt ℂ (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z) *
      Complex.Gamma z) s
    exact (hdCpow.const_mul (2 : ℂ)).mul hdG
  have hLD : logDeriv (fun z : ℂ => D ^ (z / 2)) s =
      (Real.log (absoluteDiscriminant K) : ℂ) / 2 := by
    have h := logDeriv_comp (f := fun z : ℂ => D ^ z)
      (g := fun z : ℂ => z / 2) (x := s)
      (differentiableAt_id.const_cpow (Or.inl hD)) hhalf.differentiableAt
    simpa only [Function.comp_def, Complex.logDeriv_const_cpow hD, hhalf.deriv,
      hDlog, mul_one_div] using h
  have hLRpow : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
      -(Real.log Real.pi : ℂ) / 2 := by
    have h := logDeriv_comp (f := fun z : ℂ => (Real.pi : ℂ) ^ z)
      (g := fun z : ℂ => -z / 2) (x := s)
      (differentiableAt_id.const_cpow (Or.inl hpi)) hneghalf.differentiableAt
    rw [Complex.logDeriv_const_cpow hpi, hneghalf.deriv, hlogpi] at h
    simpa only [Function.comp_def, neg_div, mul_neg, mul_one_div] using h
  have hLCpow : logDeriv (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) s =
      -(Real.log (2 * Real.pi) : ℂ) := by
    have h := logDeriv_comp (f := fun z : ℂ => (2 * (Real.pi : ℂ)) ^ z)
      (g := fun z : ℂ => -z) (x := s)
      (differentiableAt_id.const_cpow (Or.inl hpi₂)) hneg.differentiableAt
    simpa only [Function.comp_def, Complex.logDeriv_const_cpow hpi₂, hneg.deriv,
      hlogpi₂, mul_neg, mul_one] using h
  have hLGhalf : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s =
      (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2 := by
    have h := logDeriv_comp (g := fun z : ℂ => z / 2) (x := s)
      hdGhalf hhalf.differentiableAt
    simpa only [Function.comp_def, hhalf.deriv, logDeriv_apply, mul_one_div] using h
  have hLR : logDeriv Complex.Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 +
      (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2 := by
    change logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) *
      Complex.Gamma (z / 2)) s = _
    rw [logDeriv_fun_mul s hRpow hGhalf hdRpow hdGcomp, hLRpow, hLGhalf]
  have hLC : logDeriv Complex.Gammaℂ s = -(Real.log (2 * Real.pi) : ℂ) +
      deriv Complex.Gamma s / Complex.Gamma s := by
    change logDeriv (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z) *
      Complex.Gamma z) s = _
    have hconst := logDeriv_const_mul (f := fun z : ℂ =>
      (2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z) s (2 : ℂ) two_ne_zero
    rw [show (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z) =
      (fun z : ℂ => 2 * ((2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z)) by
        funext z; ring, hconst]
    rw [logDeriv_fun_mul s hCpow hG hdCpow hdG, hLCpow, logDeriv_apply]
  let r₁ := InfinitePlace.nrRealPlaces K
  let r₂ := InfinitePlace.nrComplexPlaces K
  have hfun : dedekindPrefactor K = fun z : ℂ => D ^ (z / 2) *
      (Complex.Gammaℝ z ^ r₁ * Complex.Gammaℂ z ^ r₂) := rfl
  have hP : dedekindPrefactor K s ≠ 0 := by
    rw [hfun]
    exact mul_ne_zero hDpow (mul_ne_zero (pow_ne_zero r₁ hR) (pow_ne_zero r₂ hC))
  have hdP : DifferentiableAt ℂ (dedekindPrefactor K) s := by
    rw [hfun]
    exact hdD.mul ((hdR.pow r₁).mul (hdC.pow r₂))
  refine ⟨hdP, hP, ?_⟩
  change logDeriv (dedekindPrefactor K) s = _
  rw [hfun, logDeriv_fun_mul (f := fun z : ℂ => D ^ (z / 2))
      (g := fun z : ℂ => Complex.Gammaℝ z ^ r₁ * Complex.Gammaℂ z ^ r₂) s hDpow
      (mul_ne_zero (pow_ne_zero r₁ hR) (pow_ne_zero r₂ hC)) hdD
      ((hdR.pow r₁).mul (hdC.pow r₂)),
    logDeriv_fun_mul (f := fun z : ℂ => Complex.Gammaℝ z ^ r₁)
      (g := fun z : ℂ => Complex.Gammaℂ z ^ r₂) s (pow_ne_zero r₁ hR) (pow_ne_zero r₂ hC)
      (hdR.pow r₁) (hdC.pow r₂),
    logDeriv_fun_pow hdR r₁, logDeriv_fun_pow hdC r₂, hLD, hLR, hLC]
  dsimp [r₁, r₂]
  ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
