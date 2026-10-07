import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ScaledKernel
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ExpLinearDerivatives
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ProductDifference

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

noncomputable def pd7dZLinear : PDPlane →L[ℝ] ℝ :=
  PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 2 => ℝ) 1

noncomputable def pd7dZetaLinear : PDPlane →L[ℝ] ℝ :=
  PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 2 => ℝ) 0

noncomputable def pd7dDifferenceLinear (X : ℝ) : PDPlane →L[ℝ] ℝ :=
  pd7dZLinear + (1 / X) • pd7dZetaLinear

lemma pd7dZLinear_apply (u : PDPlane) : pd7dZLinear u = u 1 := rfl
lemma pd7dZetaLinear_apply (u : PDPlane) : pd7dZetaLinear u = u 0 := rfl

lemma pd7dDifferenceLinear_apply (X : ℝ) (u : PDPlane) :
    pd7dDifferenceLinear X u = u 1 + u 0 / X := by
  simp only [pd7dDifferenceLinear, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    pd7dZLinear_apply, pd7dZetaLinear_apply, smul_eq_mul]
  ring

lemma pd7dScaledDifference_eq (X : ℝ) (u : PDPlane) :
    pd7dScaledDifference X u = X * (Real.exp (pd7dDifferenceLinear X u) - Real.exp (pd7dZLinear u)) := by
  rw [pd7dDifferenceLinear_apply, pd7dZLinear_apply, Real.exp_add]
  unfold pd7dScaledDifference
  ring

lemma pd7dScaledDifference_iteratedFDeriv_apply (X : ℝ) (n : ℕ) (u : PDPlane) (m : Fin n → PDPlane) :
    iteratedFDeriv ℝ n (pd7dScaledDifference X) u m =
      X * (Real.exp (pd7dDifferenceLinear X u) * ∏ i : Fin n, pd7dDifferenceLinear X (m i) -
        Real.exp (pd7dZLinear u) * ∏ i : Fin n, pd7dZLinear (m i)) := by
  have h₁ : ContDiff ℝ n (fun y => Real.exp (pd7dDifferenceLinear X y)) :=
    Real.contDiff_exp.comp (pd7dDifferenceLinear X).contDiff
  have h₀ : ContDiff ℝ n (fun y => Real.exp (pd7dZLinear y)) :=
    Real.contDiff_exp.comp pd7dZLinear.contDiff
  have hfun : pd7dScaledDifference X = fun y => X •
      (((fun z => Real.exp (pd7dDifferenceLinear X z)) -
        (fun z => Real.exp (pd7dZLinear z))) y) := by
    funext y
    rw [pd7dScaledDifference_eq]
    rfl
  rw [hfun]
  change (iteratedFDeriv ℝ n (X •
    ((fun z => Real.exp (pd7dDifferenceLinear X z)) -
      (fun z => Real.exp (pd7dZLinear z)))) u) m = _
  rw [iteratedFDeriv_const_smul_apply (a := X)
      (f := (fun z => Real.exp (pd7dDifferenceLinear X z)) - (fun z => Real.exp (pd7dZLinear z)))
      (h₁.sub h₀).contDiffAt,
    iteratedFDeriv_sub_apply h₁.contDiffAt h₀.contDiffAt,
    pd7d_iteratedFDeriv_exp_linear, pd7d_iteratedFDeriv_exp_linear]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
    pd7dExpTensor_apply, smul_eq_mul]

lemma pd7d_plane_coordinate_norm_le (u : PDPlane) (i : Fin 2) : |u i| ≤ ‖u‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i

lemma pd7d_difference_linear_bounds (X : ℝ) (hX : 1 ≤ X) (u : PDPlane) :
    |pd7dDifferenceLinear X u| ≤ 2 * ‖u‖ ∧ |pd7dZLinear u| ≤ 2 * ‖u‖ ∧
      |pd7dDifferenceLinear X u - pd7dZLinear u| ≤ (1 / X) * ‖u‖ := by
  have hXp : 0 < X := by linarith
  have hXi : 0 ≤ 1 / X := by positivity
  have hXione : 1 / X ≤ 1 := (div_le_one hXp).2 hX
  have hζ := pd7d_plane_coordinate_norm_le u 0
  have hz := pd7d_plane_coordinate_norm_le u 1
  rw [pd7dDifferenceLinear_apply, pd7dZLinear_apply]
  refine ⟨?_, by linarith [norm_nonneg u], ?_⟩
  · calc
      _ ≤ |u 1| + |u 0 / X| := by simpa only [Real.norm_eq_abs] using norm_add_le (u 1) (u 0 / X)
      _ ≤ ‖u‖ + (1 / X) * ‖u‖ := by
        rw [abs_div, abs_of_pos hXp]
        exact add_le_add hz (by
          simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hζ hXi)
      _ ≤ 2 * ‖u‖ := by nlinarith [mul_le_mul_of_nonneg_right hXione (norm_nonneg u)]
  · rw [add_sub_cancel_left, abs_div, abs_of_pos hXp]
    simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hζ hXi

lemma pd7d_scaled_difference_derivative_norm_le (X R E : ℝ) (hX : 1 ≤ X)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (u : PDPlane)
    (hg : |pd7dScaledDifference X u| ≤ R)
    (he : Real.exp (pd7dDifferenceLinear X u) ≤ E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (pd7dScaledDifference X) u‖ ≤ R + (n : ℝ) * E * 2 ^ n := by
  have hXp : 0 < X := by linarith
  have hXi : 0 ≤ 1 / X := by positivity
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro m
  let A := ∏ i : Fin n, pd7dDifferenceLinear X (m i)
  let B := ∏ i : Fin n, pd7dZLinear (m i)
  let W := ∏ i : Fin n, ‖m i‖
  have hW : 0 ≤ W := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hB : |B| ≤ W := by
    dsimp [B, W]
    rw [← Real.norm_eq_abs, norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i hi
    rw [pd7dZLinear_apply, Real.norm_eq_abs]
    exact pd7d_plane_coordinate_norm_le (m i) 1
  have hdiff : |A - B| ≤ (n : ℝ) * (1 / X) * 2 ^ n * W :=
    pd7d_weighted_prod_difference 2 (1 / X) (by norm_num) hXi n
      (fun i => pd7dDifferenceLinear X (m i)) (fun i => pd7dZLinear (m i))
      (fun i => ‖m i‖) (fun _ => norm_nonneg _)
      (fun i => (pd7d_difference_linear_bounds X hX (m i)).1)
      (fun i => (pd7d_difference_linear_bounds X hX (m i)).2.1)
      (fun i => (pd7d_difference_linear_bounds X hX (m i)).2.2)
  have hsplit : X * (Real.exp (pd7dDifferenceLinear X u) * A - Real.exp (pd7dZLinear u) * B) =
      pd7dScaledDifference X u * B + X * Real.exp (pd7dDifferenceLinear X u) * (A - B) := by
    rw [pd7dScaledDifference_eq]
    ring
  have hfirst : |pd7dScaledDifference X u| * |B| ≤ R * W :=
    mul_le_mul hg hB (abs_nonneg _) hR
  have hsecond : |X * Real.exp (pd7dDifferenceLinear X u)| * |A - B| ≤
      (n : ℝ) * E * 2 ^ n * W := by
    rw [abs_mul, abs_of_pos hXp, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (X * E) * ((n : ℝ) * (1 / X) * 2 ^ n * W) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he hXp.le) hdiff (abs_nonneg _)
          (mul_nonneg hXp.le hE)
      _ = _ := by field_simp <;> ring
  rw [pd7dScaledDifference_iteratedFDeriv_apply, Real.norm_eq_abs]
  change |X * (Real.exp (pd7dDifferenceLinear X u) * A - Real.exp (pd7dZLinear u) * B)| ≤ _
  rw [hsplit]
  calc
    _ ≤ |pd7dScaledDifference X u * B| + |X * Real.exp (pd7dDifferenceLinear X u) * (A - B)| := by
      simpa only [Real.norm_eq_abs] using norm_add_le
        (pd7dScaledDifference X u * B) (X * Real.exp (pd7dDifferenceLinear X u) * (A - B))
    _ ≤ R * W + (n : ℝ) * E * 2 ^ n * W := by
      rw [abs_mul, abs_mul]
      exact add_le_add hfirst hsecond
    _ = _ := by dsimp [W]; ring

end ArtinPrimitiveRoots.TypeII.PD
