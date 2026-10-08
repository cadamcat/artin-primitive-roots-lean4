import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.Decay
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

/-- The smoothing kernel on positive multiplicative coordinates, extended by zero. -/
def smoothingKernel (C A : ℝ) (r : ℕ) (T : ℝ) : ℂ :=
  if 0 < T then smoothingLogKernel C A r (Real.log T) else 0

private theorem exp_abs_log_eq_min (T N : ℝ) (hT : 0 < T) :
    Real.exp (-|N| * |Real.log T|) = min (T ^ N) (T ^ (-N)) := by
  rw [Real.rpow_def_of_pos hT N, Real.rpow_def_of_pos hT (-N)]
  have ha : -|N| * |Real.log T| = -|Real.log T * N| := by rw [abs_mul]; ring
  rw [ha, mul_neg]
  by_cases hx : 0 ≤ Real.log T * N
  · rw [abs_of_nonneg hx,
      min_eq_right (Real.exp_le_exp.mpr (by linarith))]
  · rw [abs_of_nonpos (lt_of_not_ge hx).le, neg_neg,
      min_eq_left (Real.exp_le_exp.mpr (by linarith))]

/-- The positive-coordinate kernel has the exact regularity and two-ended
log-derivative bounds required for Gaussian smoothing. -/
theorem smoothing_kernel_regular (C A : ℝ) (hC : 0 < C) (hA : 0 < A) (r : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (smoothingKernel C A r) (Set.Ioi 0) ∧
      ∀ (N : ℝ) (j : ℕ), ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 < T →
        ‖iteratedDeriv j (fun x : ℝ => smoothingKernel C A r (Real.exp x)) (Real.log T)‖ ≤
          B * min (T ^ N) (T ^ (-N)) := by
  have heq : (fun x : ℝ => smoothingKernel C A r (Real.exp x)) =
      smoothingLogKernel C A r := by
    funext x
    rw [smoothingKernel, ite_eq_left (Real.exp_pos x), Real.log_exp]
  have hlog : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.log (Set.Ioi 0) :=
    Real.contDiffOn_log.mono (by intro T hT; simpa using ne_of_gt hT)
  constructor
  · apply ((smoothing_log_kernel_smooth C A hC hA r).1.comp_contDiffOn hlog).congr
    intro T hT
    rw [smoothingKernel, ite_eq_left (show 0 < T from hT)]
    rfl
  · intro N j
    obtain ⟨B, hB, hbound⟩ := smoothing_log_kernel_decay C A hC hA r N j
    refine ⟨B, hB, ?_⟩
    intro T hT
    rw [heq]
    have hh := hbound (Real.log T)
    rw [exp_abs_log_eq_min T N hT] at hh
    exact hh

end ArtinPrimitiveRoots.Proofs.thsol_smooth
