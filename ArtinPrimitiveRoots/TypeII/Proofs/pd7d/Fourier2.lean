import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open scoped Topology FourierTransform
set_option autoImplicit false

abbrev PDPlane := EuclideanSpace ℝ (Fin 2)

noncomputable def pd7dFourier2 (f : PDPlane → ℂ) (v : PDPlane) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) ^ 2 * 𝓕 f ((2 * Real.pi)⁻¹ • v)

lemma pd7dFourier2_eq_integral (f : PDPlane → ℂ) (v : PDPlane) :
    pd7dFourier2 f v = ((1 / (2 * Real.pi) : ℝ) : ℂ) ^ 2 *
      ∫ u : PDPlane, f u * Complex.exp (-Complex.I * (inner ℝ u v : ℂ)) := by
  unfold pd7dFourier2
  rw [Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [inner_smul_right, smul_eq_mul]
  have harg : (((-2 * Real.pi * ((2 * Real.pi)⁻¹ * inner ℝ u v) : ℝ) : ℂ) * Complex.I) =
      -Complex.I * (inner ℝ u v : ℂ) := by
    push_cast
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [harg]
  ring

lemma pd7d_fourier2_inversion (f : PDPlane → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hsupp : HasCompactSupport f)
    (z : PDPlane) :
    f z = ∫ v : PDPlane, pd7dFourier2 f v * Complex.exp (Complex.I * (inner ℝ z v : ℂ)) := by
  let F : SchwartzMap PDPlane ℂ := hsupp.toSchwartzMap hf
  let q : ℝ := 2 * Real.pi
  let H := fun v : PDPlane => pd7dFourier2 f v * Complex.exp (Complex.I * (inner ℝ z v : ℂ))
  have hq : 0 < q := by dsimp [q]; positivity
  have hchange : (∫ v : PDPlane, H v) = q ^ 2 • ∫ w : PDPlane, H (q • w) := by
    have hh := Measure.integral_comp_smul volume H q
    rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hq))] at hh
    calc
      _ = q ^ 2 • ((q ^ 2)⁻¹ • ∫ v : PDPlane, H v) := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hq)), one_smul]
      _ = _ := by rw [← hh]
  have hscaled (w : PDPlane) : q ^ 2 • H (q • w) =
      Complex.exp (((q * inner ℝ w z : ℝ) : ℂ) * Complex.I) * 𝓕 f w := by
    dsimp [H, pd7dFourier2]
    have hvec : (2 * Real.pi)⁻¹ • (q • w) = w := by
      dsimp [q]
      rw [smul_smul, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]
    rw [hvec, inner_smul_right]
    have harg : Complex.I * ((q * inner ℝ z w : ℝ) : ℂ) =
        ((q * inner ℝ w z : ℝ) : ℂ) * Complex.I := by
      rw [real_inner_comm z w]
      ring
    rw [harg]
    try simp only [smul_eq_mul]
    dsimp [q]
    push_cast
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hInv : 𝓕⁻ (𝓕 f) z = f z := by
    have hFt : 𝓕 f = ((𝓕 F : SchwartzMap PDPlane ℂ) : PDPlane → ℂ) := by
      rw [SchwartzMap.fourier_coe]
      rfl
    exact congrFun (hf.continuous.fourierInv_fourier_eq F.integrable
      (by rw [hFt]; exact (𝓕 F : SchwartzMap PDPlane ℂ).integrable)) z
  have hInvIntegral : 𝓕⁻ (𝓕 f) z =
      ∫ w : PDPlane, Complex.exp (((q * inner ℝ w z : ℝ) : ℂ) * Complex.I) * 𝓕 f w := by
    rw [Real.fourierInv_eq']
    rfl
  calc
    f z = 𝓕⁻ (𝓕 f) z := hInv.symm
    _ = ∫ w : PDPlane, Complex.exp (((q * inner ℝ w z : ℝ) : ℂ) * Complex.I) * 𝓕 f w := hInvIntegral
    _ = ∫ w : PDPlane, q ^ 2 • H (q • w) := by
      apply integral_congr_ae
      exact ae_of_all _ fun w => (hscaled w).symm
    _ = ∫ v : PDPlane, H v := by rw [integral_smul, ← hchange]

end ArtinPrimitiveRoots.TypeII.PD
