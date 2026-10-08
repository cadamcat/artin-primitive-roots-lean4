import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory
open scoped FourierTransform

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.TH_S_CONV

private theorem norm_fourier_le_integral_norm {g : ℝ → ℂ} (_hg : Integrable g)
    (x : ℝ) : ‖𝓕 g x‖ ≤ ∫ t, ‖g t‖ := by
  rw [Real.fourier_eq]
  calc
    ‖∫ t, 𝐞 (-inner ℝ t x) • g t‖ ≤ ∫ t, ‖𝐞 (-inner ℝ t x) • g t‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t, ‖g t‖ := by
      congr 1
      funext t
      simp

theorem fourier_integral_norm_le_of_compactSupport {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) :
    ∫ x, ‖𝓕 g x‖ ≤
      Real.pi * (2 * (∫ x, ‖g x‖) + (∫ x, ‖iteratedDeriv 2 g x‖)) := by
  let g₁ : ℝ → ℂ := deriv g
  let g₂ : ℝ → ℂ := deriv g₁
  have hcont₁ : ContDiff ℝ 1 g₁ := by
    dsimp [g₁]
    exact hg.deriv'
  have hcont₂ : ContDiff ℝ 0 g₂ := by
    dsimp [g₂]
    exact hcont₁.deriv'
  have hcompact₁ : HasCompactSupport g₁ := by
    dsimp [g₁]
    exact hc.deriv
  have hcompact₂ : HasCompactSupport g₂ := by
    dsimp [g₂]
    exact hcompact₁.deriv
  have hInt₀ : Integrable g := hg.continuous.integrable_of_hasCompactSupport hc
  have hInt₁ : Integrable g₁ := by
    exact hcont₁.continuous.integrable_of_hasCompactSupport hcompact₁
  have hInt₂ : Integrable g₂ := by
    exact hcont₂.continuous.integrable_of_hasCompactSupport hcompact₂
  have hFreq : Integrable (fun x : ℝ => (x : ℂ) * g x) := by
    have hcont : Continuous (fun x : ℝ => (x : ℂ) * g x) :=
      Complex.continuous_ofReal.mul hg.continuous
    have hcompact : HasCompactSupport (fun x : ℝ => (x : ℂ) * g x) :=
      HasCompactSupport.mul_left hc
    exact hcont.integrable_of_hasCompactSupport hcompact
  have hFreq' : Integrable (fun x : ℝ => ‖x‖ * ‖g x‖) := by
    convert hFreq.norm using 1 <;> ext x <;> simp [norm_mul]
  have hdiffF : Differentiable ℝ (𝓕 g) := Real.differentiable_fourier hInt₀ hFreq'
  have hF₁ := Real.fourier_deriv hInt₀ (hg.differentiable (by norm_num))
    (by simpa [g₁] using hInt₁)
  have hF₂ := Real.fourier_deriv (by simpa [g₁] using hInt₁) hg.differentiable_deriv_two
    (by simpa [g₂] using hInt₂)
  have hId₂ : g₂ = iteratedDeriv 2 g := by
    simp [g₁, g₂, iteratedDeriv_succ]
  let I0 : ℝ := ∫ x, ‖g x‖
  let I2 : ℝ := ∫ x, ‖g₂ x‖
  have h0 : 0 ≤ I0 := by dsimp [I0]; exact integral_nonneg (fun _ => norm_nonneg _)
  have h2 : 0 ≤ I2 := by dsimp [I2]; exact integral_nonneg (fun _ => norm_nonneg _)
  have hPoint (x : ℝ) : ‖𝓕 g x‖ ≤
      (2 * I0 + I2) * (1 + x ^ 2)⁻¹ := by
    by_cases hx : |x| ≤ 1
    · have hden : 0 < 1 + x ^ 2 := by positivity
      have hx2 : x ^ 2 ≤ 1 := by
        calc
          x ^ 2 = |x| ^ 2 := (sq_abs x).symm
          _ ≤ 1 ^ 2 := (sq_le_sq₀ (abs_nonneg x) (by norm_num)).2 hx
          _ = 1 := by norm_num
      have hbase := norm_fourier_le_integral_norm hInt₀ x
      have hmul : I0 * (1 + x ^ 2) ≤ 2 * I0 + I2 := by
        have hprod : I0 * x ^ 2 ≤ I0 := by
          simpa [mul_one] using mul_le_mul_of_nonneg_left hx2 h0
        calc
          I0 * (1 + x ^ 2) = I0 + I0 * x ^ 2 := by ring
          _ ≤ I0 + I0 := by nlinarith [hprod]
          _ = 2 * I0 := by ring
          _ ≤ 2 * I0 + I2 := le_add_of_nonneg_right h2
      calc
        ‖𝓕 g x‖ ≤ I0 := by simpa [I0] using hbase
        _ ≤ (2 * I0 + I2) * (1 + x ^ 2)⁻¹ :=
          (le_div_iff₀ hden).2 hmul
    · have hxgt : 1 < |x| := lt_of_not_ge hx
      have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x]
      have hxne : x ≠ 0 := by
        intro h
        subst x
        norm_num at hxgt
      have hderivId : 𝓕 g₂ x =
          (2 * Real.pi * Complex.I * x) ^ 2 * 𝓕 g x := by
        rw [show g₂ = deriv (deriv g) by rfl, hF₂, hF₁]
        simp [smul_eq_mul]
        ring
      have hscalar : ‖(2 * Real.pi * Complex.I * (x : ℂ))‖ = 2 * Real.pi * |x| := by
        simp [norm_mul, Real.pi_nonneg]
      have hnorm : ‖𝓕 g₂ x‖ =
          (2 * Real.pi * |x|) ^ 2 * ‖𝓕 g x‖ := by
        rw [hderivId, norm_mul, norm_pow, hscalar]
      have hbase := norm_fourier_le_integral_norm hInt₂ x
      have hlargeDen : 1 + x ^ 2 ≤ (2 * Real.pi * |x|) ^ 2 := by
        have hpi : 1 ≤ Real.pi := by nlinarith [Real.one_le_pi_div_two]
        have hAbs : 1 ≤ |x| := hxgt.le
        have hAbsSq : 1 ≤ |x| ^ 2 := by nlinarith
        have hπsq : 1 ≤ Real.pi ^ 2 := by nlinarith
        have hprod := mul_le_mul_of_nonneg_right hπsq (sq_nonneg |x|)
        rw [sq_abs] at hprod
        nlinarith [sq_abs x]
      have hdiv : ‖𝓕 g x‖ ≤ I2 / (2 * Real.pi * |x|) ^ 2 := by
        apply (le_div_iff₀ (by positivity)).2
        calc
          ‖𝓕 g x‖ * (2 * Real.pi * |x|) ^ 2 =
              (2 * Real.pi * |x|) ^ 2 * ‖𝓕 g x‖ := by ring
          _ = ‖𝓕 g₂ x‖ := hnorm.symm
          _ ≤ I2 := by simpa [I2] using hbase
      have hcomp : I2 / (2 * Real.pi * |x|) ^ 2 ≤ I2 / (1 + x ^ 2) :=
        div_le_div_of_nonneg_left h2 (by positivity) hlargeDen
      have hcomp' : I2 / (1 + x ^ 2) ≤ (2 * I0 + I2) / (1 + x ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      calc
        ‖𝓕 g x‖ ≤ I2 / (2 * Real.pi * |x|) ^ 2 := hdiv
        _ ≤ I2 / (1 + x ^ 2) := hcomp
        _ ≤ (2 * I0 + I2) / (1 + x ^ 2) := hcomp'
        _ = (2 * I0 + I2) * (1 + x ^ 2)⁻¹ := by ring
  have hDom : Integrable (fun x : ℝ =>
      (2 * I0 + I2) * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hIntF : Integrable (fun x : ℝ => ‖𝓕 g x‖) := by
    apply hDom.mono'
    · exact hdiffF.continuous.norm.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => by simpa using hPoint x)
  calc
    ∫ x, ‖𝓕 g x‖ ≤
        ∫ x, (2 * I0 + I2) * (1 + x ^ 2)⁻¹ :=
      integral_mono_ae hIntF hDom (Filter.Eventually.of_forall hPoint)
    _ = (2 * I0 + I2) * Real.pi := by
      rw [integral_const_mul, integral_univ_inv_one_add_sq]
    _ = Real.pi * (2 * (∫ t, ‖g t‖) + (∫ t, ‖iteratedDeriv 2 g t‖)) := by
      have hI2eq : I2 = ∫ t, ‖iteratedDeriv 2 g t‖ := by
        dsimp [I2]
        rw [hId₂]
      rw [hI2eq]
      dsimp [I0]
      ring

end ArtinPrimitiveRoots.Proofs.TH_S_CONV
