import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def pd7dExpTensor (L : E →L[ℝ] ℝ) (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap (fun _ => L)

lemma pd7dExpTensor_apply (L : E →L[ℝ] ℝ) (n : ℕ) (m : Fin n → E) :
    pd7dExpTensor L n m = ∏ i : Fin n, L (m i) := by
  simp [pd7dExpTensor]

lemma pd7d_iteratedFDeriv_exp_linear (L : E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ n (fun y => Real.exp (L y)) x = Real.exp (L x) • pd7dExpTensor L n := by
  induction n generalizing x with
  | zero =>
    ext m
    simp [pd7dExpTensor_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  | succ n ih =>
    have hfun : iteratedFDeriv ℝ n (fun z => Real.exp (L z)) =
        (fun y => Real.exp (L y) • pd7dExpTensor L n) := by
      funext y
      exact ih y
    have hExp : HasFDerivAt (fun y => Real.exp (L y)) (Real.exp (L x) • L) x :=
      (Real.hasDerivAt_exp (L x)).comp_hasFDerivAt x L.hasFDerivAt
    have hd := hExp.smul_const (pd7dExpTensor L n)
    ext m
    rw [iteratedFDeriv_succ_apply_left, hfun, hd.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul, pd7dExpTensor_apply,
      Fin.prod_univ_succ, Fin.tail]
    ring

lemma pd7d_iteratedFDeriv_exp_linear_apply (L : E →L[ℝ] ℝ) (n : ℕ) (x : E) (m : Fin n → E) :
    iteratedFDeriv ℝ n (fun y => Real.exp (L y)) x m =
      Real.exp (L x) * ∏ i : Fin n, L (m i) := by
  rw [pd7d_iteratedFDeriv_exp_linear, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    pd7dExpTensor_apply]

lemma pd7dExpTensor_norm_le (L : E →L[ℝ] ℝ) (n : ℕ) : ‖pd7dExpTensor L n‖ ≤ ‖L‖ ^ n := by
  apply ContinuousMultilinearMap.opNorm_le_bound (pow_nonneg (norm_nonneg L) n)
  intro m
  rw [pd7dExpTensor_apply, norm_prod]
  calc
    _ ≤ ∏ i : Fin n, ‖L‖ * ‖m i‖ :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => L.le_opNorm (m i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

lemma pd7d_exp_linear_derivative_norm_le (L : E →L[ℝ] ℝ) (n : ℕ) (u : E) :
    ‖iteratedFDeriv ℝ n (fun y => Real.exp (L y)) u‖ ≤ Real.exp (L u) * ‖L‖ ^ n := by
  rw [pd7d_iteratedFDeriv_exp_linear, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (pd7dExpTensor_norm_le L n) (Real.exp_pos _).le

end ArtinPrimitiveRoots.TypeII.PD
