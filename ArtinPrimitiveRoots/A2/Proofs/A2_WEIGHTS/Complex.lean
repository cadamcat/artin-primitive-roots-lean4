import ArtinPrimitiveRoots.A2.Reflection.Missing

open MeasureTheory
open LineDeriv
open scoped FourierTransform RealInnerProductSpace

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_weights

open ArtinPrimitiveRoots A1 A2

private theorem reCoeff_temperate :
    (fun z : ℂ => (z.re : ℂ)).HasTemperateGrowth := by
  fun_prop

private theorem imCoeff_temperate :
    (fun z : ℂ => (z.im : ℂ)).HasTemperateGrowth := by
  fun_prop

private def eulerSchwartz (f : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (1 / 2 : ℂ) •
    (SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => (z.re : ℂ)) (∂_{(1 : ℂ)} f) +
      SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => (z.im : ℂ)) (∂_{Complex.I} f))

private theorem eulerSchwartz_apply (f : SchwartzMap ℂ ℂ) (z : ℂ) :
    eulerSchwartz f z = (1 / 2 : ℂ) * fderiv ℝ f z z := by
  have hz : (z.re : ℝ) • (1 : ℂ) + z.im • Complex.I = z := by
    apply Complex.ext <;> simp
  change (1 / 2 : ℂ) *
      (SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => (z.re : ℂ)) (∂_{(1 : ℂ)} f) z +
        SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => (z.im : ℂ)) (∂_{Complex.I} f) z) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply reCoeff_temperate,
    SchwartzMap.smulLeftCLM_apply_apply imCoeff_temperate,
    SchwartzMap.lineDerivOp_apply_eq_fderiv (1 : ℂ) f z,
    SchwartzMap.lineDerivOp_apply_eq_fderiv Complex.I f z]
  have hlin : fderiv ℝ f z z =
      z.re • fderiv ℝ f z 1 + z.im • fderiv ℝ f z Complex.I := by
    calc
      fderiv ℝ f z z = fderiv ℝ f z ((z.re : ℝ) • (1 : ℂ) + z.im • Complex.I) := by rw [hz]
      _ = _ := by rw [map_add, map_smul, map_smul]
  rw [hlin]
  change (1 / 2 : ℂ) * ((z.re : ℂ) * fderiv ℝ f z 1 +
      (z.im : ℂ) * fderiv ℝ f z Complex.I) = _
  rw [Complex.real_smul, Complex.real_smul]

private def radialIter : ℕ → SchwartzMap ℂ ℂ → SchwartzMap ℂ ℂ
  | 0, f => f
  | n + 1, f => eulerSchwartz (radialIter n f)

private theorem hasDeriv_expHalf (t : ℝ) :
    HasDerivAt (fun u : ℝ => (Real.exp (u / 2) : ℂ))
      ((Real.exp (t / 2) / 2 : ℝ) : ℂ) t := by
  have hdiv : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) t := by
    convert (hasDerivAt_id t).div_const 2 using 1 <;> simp
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (u / 2))
      (Real.exp (t / 2) / 2) t := by
    convert (Real.hasDerivAt_exp (t / 2)).comp t hdiv using 1
    · funext u
      simp only [Function.comp_apply]
    · ring
  exact hexp.ofReal_comp

private theorem euler_chain (f : SchwartzMap ℂ ℂ) (z : ℂ) (t : ℝ) :
    deriv (fun u : ℝ => f ((Real.exp (u / 2) : ℂ) * z)) t =
      eulerSchwartz f ((Real.exp (t / 2) : ℂ) * z) := by
  let y : ℂ := (Real.exp (t / 2) : ℂ) * z
  have hφ := (hasDeriv_expHalf t).mul_const z
  have hf : HasFDerivAt (fun w : ℂ => f w) (fderiv ℝ f y) y :=
    f.differentiableAt.hasFDerivAt
  have hcomp := hf.comp t hφ.hasFDerivAt
  have hchain : deriv (fun u : ℝ => f ((Real.exp (u / 2) : ℂ) * z)) t =
      fderiv ℝ f y (((Real.exp (t / 2) / 2 : ℝ) : ℂ) * z) := by
    simpa [y, Function.comp_def] using hcomp.hasDerivAt.deriv
  rw [hchain, eulerSchwartz_apply]
  have hdir : (((Real.exp (t / 2) / 2 : ℝ) : ℂ) * z) = (1 / 2 : ℝ) • y := by
    dsimp [y]
    push_cast
    ring
  rw [hdir, map_smul]
  change ((1 / 2 : ℝ) : ℂ) * fderiv ℝ f y y =
      (1 / 2 : ℂ) * fderiv ℝ f y y
  push_cast
  ring

private theorem iteratedDeriv_radial (f : SchwartzMap ℂ ℂ) (n : ℕ) (z : ℂ) (t : ℝ) :
    iteratedDeriv n (fun u : ℝ => f ((Real.exp (u / 2) : ℂ) * z)) t =
      radialIter n f ((Real.exp (t / 2) : ℂ) * z) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (fun u : ℝ => f ((Real.exp (u / 2) : ℂ) * z)) =
          fun u => radialIter n f ((Real.exp (u / 2) : ℂ) * z) := by
        funext u
        exact ih u
      rw [hfun]
      simpa [radialIter] using euler_chain (radialIter n f) z t

private theorem normDeriv_eq_radialIter (f : SchwartzMap ℂ ℂ) (n : ℕ) (z : ℂ) :
    A1.normDeriv n f z = radialIter n f z := by
  unfold A1.normDeriv
  have h := iteratedDeriv_radial f n z 0
  simpa [Complex.exp_zero] using h

private def fourierScale (z : ℂ) : ℂ := (-2 : ℝ) • star z

private theorem fourierScale_temperate :
    (fourierScale : ℂ → ℂ).HasTemperateGrowth := by
  have hconj : (fun z : ℂ => star z).HasTemperateGrowth := by
    have hconj0 := Complex.conjLIE.toContinuousLinearMap.hasTemperateGrowth
    have heq : (fun z : ℂ => star z) = fun z => Complex.conjLIE z := by
      funext z
      simp [Complex.star_def, Complex.conjLIE_apply]
    rw [heq]
    exact hconj0
  change (fun z : ℂ => (-2 : ℝ) • star z).HasTemperateGrowth
  exact (Function.HasTemperateGrowth.const (-2 : ℝ)).smul hconj

private theorem fourierScale_upper :
    ∃ k : ℕ, ∃ C : ℝ, ∀ z : ℂ, ‖z‖ ≤ C * (1 + ‖fourierScale z‖) ^ k := by
  refine ⟨1, 1, ?_⟩
  intro z
  have hz : ‖fourierScale z‖ = 2 * ‖z‖ := by
    simp [fourierScale, Complex.real_smul]
  rw [hz]
  nlinarith [norm_nonneg z]

private def complexFourierSchwartz (f : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  SchwartzMap.compCLM ℂ fourierScale_temperate fourierScale_upper (𝓕 f)

private theorem complexFourierSchwartz_apply (f : SchwartzMap ℂ ℂ) (z : ℂ) :
    complexFourierSchwartz f z = (𝓕 f) (fourierScale z) := by
  simp [complexFourierSchwartz, SchwartzMap.compCLM_apply, fourierScale_temperate,
    fourierScale_upper]

private theorem complexFourierSchwartz_eq_integral (f : SchwartzMap ℂ ℂ) (z : ℂ) :
    complexFourierSchwartz f z = ∫ x : ℂ, f x * A1.psiC (-(x * z)) := by
  rw [complexFourierSchwartz_apply, SchwartzMap.fourier_coe f, Real.fourier_eq']
  have hinner (x : ℂ) : inner ℝ x (fourierScale z) = -2 * (x * z).re := by
    change inner ℝ x ((-2 : ℝ) • star z) = _
    rw [inner_smul_right_eq_smul, Complex.inner]
    simp [fourierScale, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  apply integral_congr_ae
  filter_upwards with x
  have hphase :
      Complex.exp ((↑(-2 * Real.pi * inner ℝ x (fourierScale z)) * Complex.I)) =
        A1.psiC (-(x * z)) := by
    rw [hinner x]
    simp [A1.psiC, Complex.neg_re]
    ring
  rw [hphase]
  simp only [smul_eq_mul]
  ring

private theorem radialSchwartz_weight_bound (g : SchwartzMap ℂ ℂ) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖g z‖ * Complex.normSq z ^ σ ≤ C * bridgeComplexMajorant σ z := by
  obtain ⟨n, hn⟩ := exists_nat_gt (σ + 3)
  let C0 : ℝ := max ((SchwartzMap.seminorm ℂ 0 0) g) 0
  let Cn : ℝ := max ((SchwartzMap.seminorm ℂ (2 * n) 0) g) 0
  let p : ℝ := σ + 3
  let C : ℝ := max C0 Cn * 2 ^ p
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hCn : 0 ≤ Cn := le_max_right _ _
  have hp : 0 < p := by dsimp [p]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro z
  by_cases hz : z = 0
  · subst z
    simp [bridgeComplexMajorant, hσ.ne']
  · have hqpos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
    have hqnonneg : 0 ≤ Complex.normSq z := le_of_lt hqpos
    have hnorm : ‖g z‖ ≤ C0 := by
      have h := SchwartzMap.norm_le_seminorm ℂ g z
      exact h.trans (le_max_left _ _)
    have hpow : Complex.normSq z ^ n = ‖z‖ ^ (2 * n) := by
      rw [Complex.normSq_eq_norm_sq, ← pow_mul]
    have hjet : Complex.normSq z ^ n * ‖g z‖ ≤ Cn := by
      rw [hpow]
      simpa only [norm_iteratedFDeriv_zero] using
        (SchwartzMap.le_seminorm ℂ (2 * n) 0 g z).trans (le_max_left _ _)
    let q : ℝ := Complex.normSq z
    have hqpos' : 0 < q := hqpos
    have hqnonneg' : 0 ≤ q := hqnonneg
    have htail : ‖g z‖ ≤ Cn * q ^ (-(n : ℝ)) := by
      have hqpow : 0 < q ^ n := pow_pos hqpos' n
      have hdiv : ‖g z‖ ≤ Cn / q ^ n := by
        apply (le_div_iff₀ hqpow).2
        simpa [q, mul_comm] using hjet
      calc
        ‖g z‖ ≤ Cn / q ^ n := hdiv
        _ = Cn * q ^ (-(n : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_natCast, Real.rpow_neg hqpos'.le]
    have hmajorant_pos : 0 < (1 + q) ^ p :=
      Real.rpow_pos_of_pos (by positivity) p
    have hsmall (hq : q ≤ 1) :
        ‖g z‖ * q ^ σ ≤ C0 * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by
      have hden : (1 + q) ^ p ≤ 2 ^ p := by
        apply Real.rpow_le_rpow (by positivity) (by linarith) hp.le
      have hpow : q ^ σ ≤ 2 ^ p * q ^ σ / (1 + q) ^ p := by
        apply (le_div_iff₀ hmajorant_pos).2
        calc
          q ^ σ * (1 + q) ^ p ≤ q ^ σ * 2 ^ p :=
            mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg hqnonneg' σ)
          _ = 2 ^ p * q ^ σ := by ring
      calc
        ‖g z‖ * q ^ σ ≤ C0 * q ^ σ :=
          mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg hqnonneg' σ)
        _ ≤ C0 * (2 ^ p * q ^ σ / (1 + q) ^ p) :=
          mul_le_mul_of_nonneg_left hpow hC0
        _ = C0 * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by ring
    have hlarge (hq : 1 ≤ q) :
        ‖g z‖ * q ^ σ ≤ Cn * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by
      have hden : (1 + q) ^ p ≤ 2 ^ p * q ^ p := by
        calc
          (1 + q) ^ p ≤ (2 * q) ^ p :=
            Real.rpow_le_rpow (by positivity) (by nlinarith) hp.le
          _ = 2 ^ p * q ^ p := Real.mul_rpow (by norm_num) hqnonneg'
      have hfactor : q ^ (-3 : ℝ) ≤ 2 ^ p * q ^ σ / (1 + q) ^ p := by
        apply (le_div_iff₀ hmajorant_pos).2
        calc
          q ^ (-3 : ℝ) * (1 + q) ^ p ≤ q ^ (-3 : ℝ) * (2 ^ p * q ^ p) :=
            mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg hqnonneg' _)
          _ = 2 ^ p * (q ^ (-3 : ℝ) * q ^ p) := by ring
          _ = 2 ^ p * q ^ (p - 3) := by
            rw [← Real.rpow_add hqpos']
            congr 2 <;> ring
          _ = 2 ^ p * q ^ σ := by dsimp [p]; ring
      have hqexp : q ^ (σ - (n : ℝ)) ≤ q ^ (-3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq (by linarith)
      have htail' : ‖g z‖ * q ^ σ ≤ Cn * q ^ (-3 : ℝ) := by
        calc
          ‖g z‖ * q ^ σ ≤ (Cn * q ^ (-(n : ℝ))) * q ^ σ :=
            mul_le_mul_of_nonneg_right htail (Real.rpow_nonneg hqnonneg' σ)
          _ = Cn * q ^ (σ - (n : ℝ)) := by
            rw [mul_assoc, ← Real.rpow_add hqpos']
            congr 1
            ring
          _ ≤ Cn * q ^ (-3 : ℝ) :=
            mul_le_mul_of_nonneg_left hqexp hCn
      calc
        ‖g z‖ * q ^ σ ≤ Cn * q ^ (-3 : ℝ) := htail'
        _ ≤ Cn * (2 ^ p * q ^ σ / (1 + q) ^ p) :=
          mul_le_mul_of_nonneg_left hfactor hCn
        _ = Cn * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by ring
    have hbound : ‖g z‖ * q ^ σ ≤ C * (q ^ σ / (1 + q) ^ p) := by
      dsimp [C]
      have hratio : 0 ≤ 2 ^ p * (q ^ σ / (1 + q) ^ p) := by positivity
      by_cases hq : q ≤ 1
      · calc
          ‖g z‖ * q ^ σ ≤ C0 * 2 ^ p * (q ^ σ / (1 + q) ^ p) := hsmall hq
          _ = C0 * (2 ^ p * (q ^ σ / (1 + q) ^ p)) := by ring
          _ ≤ max C0 Cn * (2 ^ p * (q ^ σ / (1 + q) ^ p)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hratio
          _ = max C0 Cn * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by ring
      · calc
          ‖g z‖ * q ^ σ ≤ Cn * 2 ^ p * (q ^ σ / (1 + q) ^ p) :=
            hlarge (le_of_not_ge hq)
          _ = Cn * (2 ^ p * (q ^ σ / (1 + q) ^ p)) := by ring
          _ ≤ max C0 Cn * (2 ^ p * (q ^ σ / (1 + q) ^ p)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hratio
          _ = max C0 Cn * 2 ^ p * (q ^ σ / (1 + q) ^ p) := by ring
    simpa [bridgeComplexMajorant, q, p, hz] using hbound

theorem complexFourierDerivative_integrable (f : SchwartzMap ℂ ℂ) (j : ℕ)
    (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun z : ℂ =>
      ‖A1.normDeriv j (fun y : ℂ => ∫ x : ℂ, f x * A1.psiC (-(x * y))) z‖ *
        Complex.normSq z ^ σ) A1.Theta.mulHaarC := by
  let g : SchwartzMap ℂ ℂ := radialIter j (complexFourierSchwartz f)
  have hFourier : (fun y : ℂ => ∫ x : ℂ, f x * A1.psiC (-(x * y))) =
      (complexFourierSchwartz f : ℂ → ℂ) := by
    funext y
    exact (complexFourierSchwartz_eq_integral f y).symm
  have hrad :
      (fun z : ℂ => A1.normDeriv j
        (fun y : ℂ => ∫ x : ℂ, f x * A1.psiC (-(x * y))) z) =
          (g : ℂ → ℂ) := by
    funext z
    rw [hFourier]
    exact normDeriv_eq_radialIter (complexFourierSchwartz f) j z
  have hweightCont : Continuous (fun z : ℂ => Complex.normSq z ^ σ) :=
    (Real.continuous_rpow_const hσ.le).comp Complex.continuous_normSq
  have hmeas : AEStronglyMeasurable
      (fun z : ℂ => ‖g z‖ * Complex.normSq z ^ σ) A1.Theta.mulHaarC :=
    ((g.smooth ⊤).continuous.norm.mul hweightCont).aestronglyMeasurable
  obtain ⟨C, hC, hbound⟩ := radialSchwartz_weight_bound g σ hσ
  have hdom : Integrable (fun z : ℂ => C * bridgeComplexMajorant σ z)
      A1.Theta.mulHaarC :=
    (bridgeComplexMajorant_integrable σ hσ).const_mul C
  have htarget : (fun z : ℂ =>
      ‖A1.normDeriv j (fun y : ℂ => ∫ x : ℂ, f x * A1.psiC (-(x * y))) z‖ *
        Complex.normSq z ^ σ) =
        (fun z : ℂ => ‖g z‖ * Complex.normSq z ^ σ) := by
      funext z
      rw [congrFun hrad z]
  rw [htarget]
  refine hdom.mono' hmeas ?_
  filter_upwards with z
  have ht : 0 ≤ ‖g z‖ * Complex.normSq z ^ σ :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Complex.normSq_nonneg _) σ)
  rw [Real.norm_eq_abs, abs_of_nonneg ht]
  exact hbound z

end ArtinPrimitiveRoots.Proofs.a2_weights
end
