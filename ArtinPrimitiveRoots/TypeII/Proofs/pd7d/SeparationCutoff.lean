import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ScaledKernel

namespace ArtinPrimitiveRoots.TypeII.PD

set_option autoImplicit false

noncomputable def pd7dSeparationCutoff : ContDiffBump (17 / 2 : ℝ) where
  rIn := 15 / 2
  rOut := 8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

lemma pd7d_separation_cutoff_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pd7dSeparationCutoff : ℝ → ℝ) :=
  pd7dSeparationCutoff.contDiff

lemma pd7d_separation_cutoff_support : Function.support (pd7dSeparationCutoff : ℝ → ℝ) ⊆
    Set.Icc (1 / 2 : ℝ) 32 := by
  intro y hy
  rw [pd7dSeparationCutoff.support_eq] at hy
  have hh : |y - 17 / 2| < 8 := by
    simpa only [Metric.mem_ball, Real.dist_eq, pd7dSeparationCutoff] using hy
  have h := abs_lt.mp hh
  constructor <;> linarith

lemma pd7d_separation_cutoff_one (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 16) :
    pd7dSeparationCutoff y = 1 := by
  apply pd7dSeparationCutoff.one_of_mem_closedBall
  change dist y (17 / 2 : ℝ) ≤ 15 / 2
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith [hy.1, hy.2]

end ArtinPrimitiveRoots.TypeII.PD
