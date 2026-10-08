import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.Fourier2

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII
set_option autoImplicit false

noncomputable def pd7dScaledDifference (X : ℝ) (u : PDPlane) : ℝ :=
  X * Real.exp (u 1) * (Real.exp (u 0 / X) - 1)

noncomputable def pd7dScaledKernel (κ ψ : ℝ → ℝ) (X lam : ℝ) (u : PDPlane) : ℂ :=
  (κ (Real.exp (u 1)) : ℂ) * (κ (Real.exp (u 1 + u 0 / X)) : ℂ) *
    (ψ (pd7dScaledDifference X u) : ℂ) * additiveCharacter (lam * pd7dScaledDifference X u)

lemma pd7d_abs_log_sub_le {u v : ℝ} (hu : (1 / 2 : ℝ) ≤ u) (hv : (1 / 2 : ℝ) ≤ v) :
    |Real.log u - Real.log v| ≤ 2 * |u - v| := by
  have hp : 0 < u := by linarith
  have hq : 0 < v := by linarith
  have hforward {a b : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (hab : a ≤ b) :
      Real.log b - Real.log a ≤ 2 * (b - a) := by
    have hapos : 0 < a := by linarith
    have hbpos : 0 < b := hapos.trans_le hab
    have hinv : 1 / a ≤ 2 := (div_le_iff₀ hapos).2 (by linarith)
    calc
      _ = Real.log (b / a) := (Real.log_div (ne_of_gt hbpos) (ne_of_gt hapos)).symm
      _ ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hbpos hapos)
      _ = (b - a) * (1 / a) := by field_simp <;> ring
      _ ≤ (b - a) * 2 := mul_le_mul_of_nonneg_left hinv (sub_nonneg.mpr hab)
      _ = _ := by ring
  rcases le_total u v with huv | hvu
  · have hlogs : Real.log u ≤ Real.log v := Real.log_le_log hp huv
    rw [abs_of_nonpos (sub_nonpos.mpr hlogs), abs_of_nonpos (sub_nonpos.mpr huv)]
    nlinarith [hforward hu huv]
  · have hlogs : Real.log v ≤ Real.log u := Real.log_le_log hq hvu
    rw [abs_of_nonneg (sub_nonneg.mpr hlogs), abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hforward hv hvu

lemma pd7d_scaled_kernel_support_box (κ ψ : ℝ → ℝ) (X lam R : ℝ)
    (hX : 1 ≤ X)
    (hκ : Function.support κ ⊆ Set.Icc (1 / 2 : ℝ) 32)
    (hψ : Function.support ψ ⊆ Set.Icc (-R) R) (u : PDPlane)
    (hu : u ∈ Function.support (pd7dScaledKernel κ ψ X lam)) :
    |u 0| ≤ 2 * R ∧ u 1 ∈ Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log 32) := by
  have hXpos : 0 < X := by linarith
  have hκ₁ : κ (Real.exp (u 1)) ≠ 0 := by
    intro hz
    exact hu (by simp [pd7dScaledKernel, hz])
  have hκ₂ : κ (Real.exp (u 1 + u 0 / X)) ≠ 0 := by
    intro hz
    exact hu (by simp [pd7dScaledKernel, hz])
  have hψne : ψ (pd7dScaledDifference X u) ≠ 0 := by
    intro hz
    exact hu (by simp [pd7dScaledKernel, hz])
  have hw := hκ hκ₁
  have hw' := hκ hκ₂
  have hg : |pd7dScaledDifference X u| ≤ R := abs_le.mpr (hψ hψne)
  have hlog := pd7d_abs_log_sub_le hw'.1 hw.1
  simp only [Real.log_exp] at hlog
  have hdifference : pd7dScaledDifference X u =
      X * (Real.exp (u 1 + u 0 / X) - Real.exp (u 1)) := by
    rw [Real.exp_add]
    dsimp [pd7dScaledDifference]
    ring
  have hζ : |u 0| ≤ 2 * |pd7dScaledDifference X u| := by
    have hh := mul_le_mul_of_nonneg_left hlog hXpos.le
    rw [show u 1 + u 0 / X - u 1 = u 0 / X by ring, abs_div, abs_of_pos hXpos] at hh
    rw [hdifference, abs_mul, abs_of_pos hXpos]
    have hcancel : X * (|u 0| / X) = |u 0| := by field_simp
    rw [hcancel] at hh
    nlinarith
  refine ⟨hζ.trans (mul_le_mul_of_nonneg_left hg (by norm_num)), ?_, ?_⟩
  · have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hw.1
    simpa using hh
  · have hh := Real.log_le_log (Real.exp_pos _) hw.2
    simpa using hh

lemma pd7d_plane_norm_le (u : PDPlane) : ‖u‖ ≤ |u 0| + |u 1| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [mul_nonneg (abs_nonneg (u 0)) (abs_nonneg (u 1)), sq_abs (u 0), sq_abs (u 1)]

lemma pd7d_scaled_kernel_hasCompactSupport (κ ψ : ℝ → ℝ) (X lam R : ℝ)
    (hX : 1 ≤ X) (hR : 0 ≤ R)
    (hκ : Function.support κ ⊆ Set.Icc (1 / 2 : ℝ) 32)
    (hψ : Function.support ψ ⊆ Set.Icc (-R) R) :
    HasCompactSupport (pd7dScaledKernel κ ψ X lam) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : PDPlane)
    (2 * R + |Real.log (1 / 2 : ℝ)| + |Real.log 32|))
  intro u hu
  obtain ⟨hζ, hz⟩ := pd7d_scaled_kernel_support_box κ ψ X lam R hX hκ hψ u hu
  have hzAbs : |u 1| ≤ |Real.log (1 / 2 : ℝ)| + |Real.log 32| := by
    apply abs_le.mpr
    constructor
    · linarith [hz.1, neg_abs_le (Real.log (1 / 2 : ℝ)), abs_nonneg (Real.log 32)]
    · linarith [hz.2, le_abs_self (Real.log 32), abs_nonneg (Real.log (1 / 2 : ℝ))]
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pd7d_plane_norm_le u).trans (by linarith)

lemma pd7d_scaled_kernel_contDiff (κ ψ : ℝ → ℝ) (X lam : ℝ)
    (hκ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pd7dScaledKernel κ ψ X lam) := by
  have hcoord (i : Fin 2) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : PDPlane => u i) :=
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 2 => ℝ) i).contDiff
  have hz := hcoord 1
  have hζ := hcoord 0
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pd7dScaledDifference X) := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : PDPlane => X * Real.exp (u 1) * (Real.exp (u 0 / X) - 1))
    exact (contDiff_const.mul (Real.contDiff_exp.comp hz)).mul
      ((Real.contDiff_exp.comp (hζ.div_const X)).sub contDiff_const)
  have hLeft := Complex.ofRealCLM.contDiff.comp (hκ.comp (Real.contDiff_exp.comp hz))
  have hRight := Complex.ofRealCLM.contDiff.comp
    (hκ.comp (Real.contDiff_exp.comp (hz.add (hζ.div_const X))))
  have hPsi := Complex.ofRealCLM.contDiff.comp (hψ.comp hG)
  have hArg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : PDPlane => Complex.I * ((2 * Real.pi : ℂ) *
        ((lam * pd7dScaledDifference X u : ℝ) : ℂ))) :=
    contDiff_const.mul (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hG)))
  unfold pd7dScaledKernel additiveCharacter
  exact ((hLeft.mul hRight).mul hPsi).mul (Complex.contDiff_exp.comp hArg)

lemma pd7d_scaled_kernel_fourier_inversion (κ ψ : ℝ → ℝ) (X lam R : ℝ)
    (hX : 1 ≤ X) (hR : 0 ≤ R)
    (hκ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hκsupp : Function.support κ ⊆ Set.Icc (1 / 2 : ℝ) 32)
    (hψsupp : Function.support ψ ⊆ Set.Icc (-R) R) (u : PDPlane) :
    pd7dScaledKernel κ ψ X lam u = ∫ v : PDPlane,
      pd7dFourier2 (pd7dScaledKernel κ ψ X lam) v * Complex.exp (Complex.I * (inner ℝ u v : ℂ)) :=
  pd7d_fourier2_inversion _ (pd7d_scaled_kernel_contDiff κ ψ X lam hκ hψ)
    (pd7d_scaled_kernel_hasCompactSupport κ ψ X lam R hX hR hκsupp hψsupp) u

end ArtinPrimitiveRoots.TypeII.PD
