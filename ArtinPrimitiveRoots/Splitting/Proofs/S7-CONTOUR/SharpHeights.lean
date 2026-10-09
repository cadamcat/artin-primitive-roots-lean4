import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».XiHeights
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».SharpLogDeriv

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke

/-- High unit intervals contain nonzero analytic sharp-zeta lines with cubic derivative bounds. -/
theorem sharp_good_height (K : Type*) [Field K] [NumberField K] :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, (3 ≤ a ∨ a + 1 ≤ -3) →
      ∃ T : ℝ, T ∈ Set.Icc a (a + 1) ∧
      (∀ s : ℂ, s.im = T →
        AnalyticAt ℂ (dedekindZetaSharp K) s ∧ dedekindZetaSharp K s ≠ 0) ∧
      ∀ σ : ℝ, σ ∈ Set.Icc (-1 / 2 : ℝ) 2 →
        ‖dedekindZetaLogDerivative K ((σ : ℂ) + T * Complex.I)‖ ≤
          A * (|a| + 4) ^ 3 := by
  obtain ⟨Axi, hAxi, hheight⟩ := xi_good_height K
  obtain ⟨C, hC, herror⟩ := sharp_xi_difference_bound K
  let A : ℝ := Axi + C
  have hA : 0 < A := add_pos hAxi hC
  have hcont := sharp_continuation K
  have hdXi : Differentiable ℂ (dedekindXi K) :=
    (Classical.choose_spec (dedekind_completed K)).1
  have hform : dedekindZetaSharp K = fun s : ℂ =>
      dedekindXi K s * invPrefactor K s / (s * (s - 1)) := funext hcont.2.1
  refine ⟨A, hA, ?_⟩
  intro a ha
  obtain ⟨T, hT, hxiLine, hxiBound⟩ := hheight a
  have hT₃ : 3 ≤ |T| := by
    rcases ha with hpos | hneg
    · exact (hpos.trans hT.1).trans (le_abs_self T)
    · have h : T ≤ -3 := hT.2.trans hneg
      rw [abs_of_nonpos (by linarith only [h] : T ≤ 0)]
      linarith only [h]
  have hT₀ : T ≠ 0 := by
    intro h
    simp only [h, abs_zero] at hT₃
    linarith only [hT₃]
  have hTabs : |T| ≤ |a| + 1 := by
    apply abs_le.mpr
    constructor
    · linarith [hT.1, neg_abs_le a]
    · linarith [hT.2, le_abs_self a]
  have hline (s : ℂ) (hs : s.im = T) :
      AnalyticAt ℂ (dedekindZetaSharp K) s ∧ dedekindZetaSharp K s ≠ 0 := by
    have hsim : s.im ≠ 0 := by rwa [hs]
    have hs₀ : s ≠ 0 := by
      intro h
      apply hsim
      simp [h]
    have hs₁ : s - 1 ≠ 0 := by
      intro h
      have heq : s = 1 := sub_eq_zero.mp h
      apply hsim
      simp [heq]
    refine ⟨?_, (sharp_logderiv K hsim (hxiLine s hs)).2.1⟩
    rw [hform]
    exact ((hdXi.analyticAt s).mul (hcont.1.analyticAt s)).div
      (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)) (mul_ne_zero hs₀ hs₁)
  refine ⟨T, hT, hline, ?_⟩
  intro σ hσ
  let s : ℂ := (σ : ℂ) + T * Complex.I
  have hsIm : s.im = T := by simp [s]
  have hsRe : s.re ∈ Set.Icc (-1 / 2 : ℝ) 2 := by simpa [s] using hσ
  have hxi : dedekindXi K s ≠ 0 := hxiLine s hsIm
  have herr : ‖dedekindZetaLogDerivative K s +
      deriv (dedekindXi K) s / dedekindXi K s‖ ≤ C * Real.log (2 + |T|) := by
    simpa only [hsIm] using herror s hsRe (by rwa [hsIm]) hxi
  let r : ℝ := |a| + 4
  have hr₄ : 4 ≤ r := by dsimp [r]; linarith [abs_nonneg a]
  have hr : 0 ≤ r := by linarith only [hr₄]
  have hsq : 1 ≤ r ^ 2 := by nlinarith only [hr₄]
  have hcube : r ≤ r ^ 3 := by
    calc
      r = r * 1 := by ring
      _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left hsq hr
      _ = r ^ 3 := by ring
  have hlog : Real.log (2 + |T|) ≤ r ^ 3 := by
    calc
      _ ≤ (2 + |T|) - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ r := by dsimp [r]; linarith only [hTabs]
      _ ≤ r ^ 3 := hcube
  have hxiAt : ‖deriv (dedekindXi K) s / dedekindXi K s‖ ≤ Axi * r ^ 3 :=
    hxiBound σ hσ
  calc
    ‖dedekindZetaLogDerivative K s‖ =
        ‖(dedekindZetaLogDerivative K s + deriv (dedekindXi K) s / dedekindXi K s) -
          deriv (dedekindXi K) s / dedekindXi K s‖ := by congr 1; ring
    _ ≤ ‖dedekindZetaLogDerivative K s + deriv (dedekindXi K) s / dedekindXi K s‖ +
        ‖deriv (dedekindXi K) s / dedekindXi K s‖ := norm_sub_le _ _
    _ ≤ C * Real.log (2 + |T|) + Axi * r ^ 3 := add_le_add herr hxiAt
    _ ≤ C * r ^ 3 + Axi * r ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hlog hC.le
      linarith only [h]
    _ = A * (|a| + 4) ^ 3 := by dsimp [A, r]; ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
