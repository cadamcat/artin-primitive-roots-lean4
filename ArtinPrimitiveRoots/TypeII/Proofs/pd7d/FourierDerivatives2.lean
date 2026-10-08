import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.Fourier2

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory LineDeriv
open scoped Topology FourierTransform
set_option autoImplicit false

noncomputable def pd7dPartial (i : Fin 2) : ℕ → SchwartzMap PDPlane ℂ → SchwartzMap PDPlane ℂ
  | 0, F => F
  | n + 1, F => ∂_{EuclideanSpace.single i (1 : ℝ)} (pd7dPartial i n F)

lemma pd7dFourier2_schwartz_eq (F : SchwartzMap PDPlane ℂ) (v : PDPlane) :
    pd7dFourier2 (F : PDPlane → ℂ) v = ((1 / (2 * Real.pi) : ℝ) : ℂ) ^ 2 *
      (𝓕 F : SchwartzMap PDPlane ℂ) ((2 * Real.pi)⁻¹ • v) := rfl

lemma pd7dFourier2_lineDeriv (F : SchwartzMap PDPlane ℂ) (i : Fin 2) (v : PDPlane) :
    pd7dFourier2 ((∂_{EuclideanSpace.single i (1 : ℝ)} F : SchwartzMap PDPlane ℂ) : PDPlane → ℂ) v =
      (Complex.I * (v i : ℂ)) * pd7dFourier2 (F : PDPlane → ℂ) v := by
  let m : PDPlane := EuclideanSpace.single i (1 : ℝ)
  have htemp : (fun u : PDPlane => inner ℝ u m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [pd7dFourier2_schwartz_eq, pd7dFourier2_schwartz_eq,
    SchwartzMap.fourier_lineDerivOp_eq]
  simp only [SchwartzMap.smul_apply, smul_eq_mul]
  have happ : ((SchwartzMap.smulLeftCLM ℂ
      (fun u : PDPlane => inner ℝ u (EuclideanSpace.single i (1 : ℝ))))
      (𝓕 F : SchwartzMap PDPlane ℂ)) ((2 * Real.pi)⁻¹ • v) =
      (inner ℝ ((2 * Real.pi)⁻¹ • v) (EuclideanSpace.single i (1 : ℝ))) •
        (𝓕 F : SchwartzMap PDPlane ℂ) ((2 * Real.pi)⁻¹ • v) :=
    SchwartzMap.smulLeftCLM_apply_apply htemp _ _
  rw [happ]
  have hinner : inner ℝ ((2 * Real.pi)⁻¹ • v) m = (2 * Real.pi)⁻¹ * v i := by
    dsimp [m]
    simp [inner_smul_left, EuclideanSpace.inner_single_right]
  dsimp only [m] at hinner
  rw [hinner]
  simp only [Algebra.smul_def]
  generalize hB : (𝓕 F : SchwartzMap PDPlane ℂ) ((2 * Real.pi)⁻¹ • v) = B
  push_cast
  field_simp [Real.pi_ne_zero]
  <;> exact mul_right_comm (Real.pi : ℂ) (v i : ℂ) B

lemma pd7dFourier2_partial (F : SchwartzMap PDPlane ℂ) (i : Fin 2) (n : ℕ) (v : PDPlane) :
    pd7dFourier2 (pd7dPartial i n F : PDPlane → ℂ) v =
      (Complex.I * (v i : ℂ)) ^ n * pd7dFourier2 (F : PDPlane → ℂ) v := by
  induction n with
  | zero => simp [pd7dPartial]
  | succ n ih =>
    rw [pd7dPartial, pd7dFourier2_lineDeriv, ih, pow_succ]
    ring

lemma pd7dFourier2_norm_le (f : PDPlane → ℂ) (v : PDPlane) :
    ‖pd7dFourier2 f v‖ ≤ (1 / (2 * Real.pi)) ^ 2 * ∫ u : PDPlane, ‖f u‖ := by
  unfold pd7dFourier2
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ PDPlane) f _

lemma pd7dFourier2_partial_norm (F : SchwartzMap PDPlane ℂ) (i : Fin 2) (n : ℕ) (v : PDPlane) :
    ‖pd7dFourier2 (pd7dPartial i n F : PDPlane → ℂ) v‖ =
      |v i| ^ n * ‖pd7dFourier2 (F : PDPlane → ℂ) v‖ := by
  rw [pd7dFourier2_partial, norm_mul, norm_pow, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, one_mul]

lemma pd7dFourier2_mixed_partial_norm (F : SchwartzMap PDPlane ℂ) (n : ℕ) (v : PDPlane) :
    ‖pd7dFourier2 (pd7dPartial 0 n (pd7dPartial 1 n F) : PDPlane → ℂ) v‖ =
      |v 0| ^ n * |v 1| ^ n * ‖pd7dFourier2 (F : PDPlane → ℂ) v‖ := by
  rw [pd7dFourier2_partial_norm, pd7dFourier2_partial_norm]
  ring

lemma pd7dFourier2_partial_weight_bound (F : SchwartzMap PDPlane ℂ) (i : Fin 2) (n : ℕ) (v : PDPlane) :
    |v i| ^ n * ‖pd7dFourier2 (F : PDPlane → ℂ) v‖ ≤
      (1 / (2 * Real.pi)) ^ 2 * ∫ u : PDPlane, ‖pd7dPartial i n F u‖ := by
  rw [← pd7dFourier2_partial_norm]
  exact pd7dFourier2_norm_le _ _

lemma pd7dFourier2_mixed_weight_bound (F : SchwartzMap PDPlane ℂ) (n : ℕ) (v : PDPlane) :
    |v 0| ^ n * |v 1| ^ n * ‖pd7dFourier2 (F : PDPlane → ℂ) v‖ ≤
      (1 / (2 * Real.pi)) ^ 2 * ∫ u : PDPlane, ‖pd7dPartial 0 n (pd7dPartial 1 n F) u‖ := by
  rw [← pd7dFourier2_mixed_partial_norm]
  exact pd7dFourier2_norm_le _ _

end ArtinPrimitiveRoots.TypeII.PD
