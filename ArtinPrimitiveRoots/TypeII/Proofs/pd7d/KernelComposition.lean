import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.KernelSupportData
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.PhaseDerivatives

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma pd7d_composition_jet_bound (f : E → ℝ) (g : ℝ → F) (u : E) (C D : ℝ)
    (n k : ℕ) (hk : k ≤ n) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (houter : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ C)
    (hinner : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f u‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ k (g ∘ f) u‖ ≤
      ∑ i ∈ Finset.range (n + 1), (i.factorial : ℝ) * C * D ^ i := by
  have hh := norm_iteratedFDeriv_comp_le hg hf (by simp : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)) u
    (fun i hi => houter i (hi.trans hk) (f u)) (fun i hi₁ hi₂ => hinner i hi₁ (hi₂.trans hk))
  refine hh.trans ?_
  apply Finset.single_le_sum (a := k)
  · intro i hi
    positivity
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)

lemma pd7d_exp_linear_jet_bound (L : E →L[ℝ] ℝ) (u : E) (B C : ℝ)
    (hB : 1 ≤ B) (hC : 1 ≤ C) (hL : ‖L‖ ≤ B) (he : Real.exp (L u) ≤ C)
    (i : ℕ) (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun y => Real.exp (L y)) u‖ ≤ (C * B) ^ i := by
  have hC0 : 0 ≤ C := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hpowC : C ≤ C ^ i := by
    simpa only [pow_one] using pow_le_pow_right₀ hC hi
  calc
    _ ≤ Real.exp (L u) * ‖L‖ ^ i := pd7d_exp_linear_derivative_norm_le L i u
    _ ≤ C * B ^ i := mul_le_mul he (pow_le_pow_left₀ (norm_nonneg _) hL i)
      (pow_nonneg (norm_nonneg _) i) hC0
    _ ≤ C ^ i * B ^ i := mul_le_mul_of_nonneg_right hpowC (pow_nonneg hB0 i)
    _ = _ := (mul_pow C B i).symm

lemma pd7d_scaled_difference_contDiff (X : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pd7dScaledDifference X) := by
  have hfun : pd7dScaledDifference X = fun u => X *
      (Real.exp (pd7dDifferenceLinear X u) - Real.exp (pd7dZLinear u)) := by
    funext u
    exact pd7dScaledDifference_eq X u
  rw [hfun]
  exact contDiff_const.mul
    ((Real.contDiff_exp.comp (pd7dDifferenceLinear X).contDiff).sub
      (Real.contDiff_exp.comp pd7dZLinear.contDiff))

lemma pd7dDifferenceLinear_norm_le (X : ℝ) (hX : 1 ≤ X) : ‖pd7dDifferenceLinear X‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [Real.norm_eq_abs]
  exact (pd7d_difference_linear_bounds X hX u).1

lemma pd7dZLinear_norm_le : ‖pd7dZLinear‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [pd7dZLinear_apply, Real.norm_eq_abs, one_mul]
  exact pd7d_plane_coordinate_norm_le u 1

end ArtinPrimitiveRoots.TypeII.PD
