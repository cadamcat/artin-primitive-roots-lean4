import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.SeparationCutoff

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII
set_option autoImplicit false

noncomputable def pd7dPlanePoint (a b : ℝ) : PDPlane := WithLp.toLp 2 ![a, b]

lemma pd7dPlanePoint_zero (a b : ℝ) : pd7dPlanePoint a b 0 = a := rfl
lemma pd7dPlanePoint_one (a b : ℝ) : pd7dPlanePoint a b 1 = b := rfl

lemma pd7dPlanePoint_inner (a b : ℝ) (v : PDPlane) :
    inner ℝ (pd7dPlanePoint a b) v = a * v 0 + b * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [pd7dPlanePoint_zero, pd7dPlanePoint_one, Real.inner_apply]

lemma pd7d_scaled_kernel_mellin (κ ψ : ℝ → ℝ) (X lam R w w' : ℝ)
    (hX : 1 ≤ X) (hR : 0 ≤ R)
    (hκ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hκsupp : Function.support κ ⊆ Set.Icc (1 / 2 : ℝ) 32)
    (hψsupp : Function.support ψ ⊆ Set.Icc (-R) R)
    (hκone : ∀ y ∈ Set.Icc (1 : ℝ) 16, κ y = 1)
    (hw : w ∈ Set.Icc (1 : ℝ) 16) (hw' : w' ∈ Set.Icc (1 : ℝ) 16) :
    (ψ (X * (w - w')) : ℂ) * additiveCharacter (lam * X * (w - w')) =
      ∫ v : PDPlane, pd7dFourier2 (pd7dScaledKernel κ ψ X lam) v *
        Complex.exp (Complex.I * ((X * v 0 * Real.log w +
          (v 1 - X * v 0) * Real.log w' : ℝ) : ℂ)) := by
  have hXp : 0 < X := by linarith
  have hwp : 0 < w := by linarith [hw.1]
  have hw'p : 0 < w' := by linarith [hw'.1]
  let u := pd7dPlanePoint (X * Real.log (w / w')) (Real.log w')
  have hquot : (X * Real.log (w / w')) / X = Real.log (w / w') := by field_simp
  have hexp₀ : Real.exp (u 1) = w' := by
    rw [pd7dPlanePoint_one, Real.exp_log hw'p]
  have hexp₁ : Real.exp (u 1 + u 0 / X) = w := by
    rw [pd7dPlanePoint_one, pd7dPlanePoint_zero, hquot, Real.exp_add,
      Real.exp_log hw'p, Real.exp_log (div_pos hwp hw'p)]
    field_simp
  have hdiff : pd7dScaledDifference X u = X * (w - w') := by
    unfold pd7dScaledDifference
    rw [pd7dPlanePoint_one, pd7dPlanePoint_zero, hquot,
      Real.exp_log hw'p, Real.exp_log (div_pos hwp hw'p)]
    field_simp
    <;> ring
  have hvalue : pd7dScaledKernel κ ψ X lam u =
      (ψ (X * (w - w')) : ℂ) * additiveCharacter (lam * X * (w - w')) := by
    unfold pd7dScaledKernel
    rw [hexp₀, hexp₁, hdiff, hκone w hw, hκone w' hw']
    simp only [Complex.ofReal_one, one_mul, mul_assoc]
  have hinv := pd7d_scaled_kernel_fourier_inversion κ ψ X lam R hX hR hκ hψ hκsupp hψsupp u
  rw [hvalue] at hinv
  refine hinv.trans ?_
  apply integral_congr_ae
  filter_upwards [] with v
  have hinner : inner ℝ u v = X * v 0 * Real.log w + (v 1 - X * v 0) * Real.log w' := by
    rw [pd7dPlanePoint_inner, Real.log_div (ne_of_gt hwp) (ne_of_gt hw'p)]
    ring
  rw [hinner]

end ArtinPrimitiveRoots.TypeII.PD
