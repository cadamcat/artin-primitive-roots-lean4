import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_weights_sol

theorem exists_positive_W1 :
    ∃ W1 : ℝ → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W1 ∧
      HasCompactSupport W1 ∧
      tsupport W1 ⊆ Set.Ioi 0 ∧
      (∀ t, (W1 t).im = 0 ∧ 0 ≤ (W1 t).re) ∧
      ∃ t, W1 t ≠ 0 := by
  let b : ContDiffBump (1 : ℝ) :=
    { rIn := 1 / 4
      rOut := 1 / 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let W1 : ℝ → ℂ := fun t => (b t : ℂ)
  have hsupport : Function.support W1 = Function.support b := by
    ext t
    simp [W1, Function.mem_support]
  have htsupport : tsupport W1 = tsupport b := congrArg closure hsupport
  refine ⟨W1, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp b.contDiff
  · change IsCompact (tsupport W1)
    rw [htsupport]
    exact b.hasCompactSupport
  · rw [htsupport, b.tsupport_eq]
    intro t ht
    have hdist : |t - 1| ≤ 1 / 2 := by
      simpa [Real.dist_eq, b] using ht
    have hlower := (abs_le.mp hdist).1
    change 0 < t
    linarith
  · intro t
    exact ⟨Complex.ofReal_im _, by simpa [W1] using b.nonneg' t⟩
  · refine ⟨1, ?_⟩
    have hb : b 1 = 1 := b.one_of_mem_closedBall
      (Metric.mem_closedBall_self b.rIn_pos.le)
    simp [W1, hb]

end ArtinPrimitiveRoots.Proofs.a2_weights_sol
