import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
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

theorem exists_positive_arch_factor :
    ∃ f : SchwartzMap ℂ ℂ,
      HasCompactSupport f ∧
      (∀ z ∈ tsupport f, z ≠ 0) ∧
      (∀ z, (f z).im = 0 ∧ 0 ≤ (f z).re) ∧
      0 < (∫ z : ℂ, f z).re ∧
      0 < (∫ z : ℂ, f z * (Complex.normSq z : ℂ) ^ (-(1 / 6 : ℂ))).re := by
  let b : ContDiffBump (1 : ℂ) :=
    { rIn := 1 / 4
      rOut := 1 / 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let h : ℂ → ℂ := fun z => (b z : ℂ)
  have hsupport : Function.support h = Function.support b := by
    ext z
    simp [h, Function.mem_support]
  have htsupport : tsupport h = tsupport b := congrArg closure hsupport
  have hcompact : HasCompactSupport h := by
    change IsCompact (tsupport h)
    rw [htsupport]
    exact b.hasCompactSupport
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : SchwartzMap ℂ ℂ := hcompact.toSchwartzMap hsmooth
  have hf (z : ℂ) : f z = (b z : ℂ) := rfl
  have hb1 : b 1 = 1 := b.one_of_mem_closedBall
    (Metric.mem_closedBall_self b.rIn_pos.le)
  have hb0 : (0 : ℂ) ∉ tsupport b := by
    rw [b.tsupport_eq]
    norm_num [Metric.mem_closedBall, dist_eq_norm, b]
  have hBpos : 0 < ∫ z : ℂ, b z :=
    integral_pos_of_integrable_nonneg_nonzero b.continuous
      (b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport)
      (fun z => b.nonneg' z) (by rw [hb1]; norm_num)
  let G : ℂ → ℝ := fun z => b z * Complex.normSq z ^ (-(1 / 6 : ℝ))
  have hGcont : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z
      have hbevent : (fun z : ℂ => b z) =ᶠ[𝓝 0] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hb0
      have hGevent : G =ᶠ[𝓝 0] fun _ : ℂ => (0 : ℝ) := by
        filter_upwards [hbevent] with z hz
        simp [G, hz]
      exact (continuousAt_const.congr hGevent.symm)
    · exact b.continuous.continuousAt.mul
        (Complex.continuous_normSq.continuousAt.rpow_const
          (Or.inl (Complex.normSq_pos.mpr hz).ne'))
  have hGcompact : HasCompactSupport G := b.hasCompactSupport.mul_right
  have hGnonneg (z : ℂ) : 0 ≤ G z :=
    mul_nonneg (b.nonneg' z) (Real.rpow_nonneg (Complex.normSq_nonneg z) _)
  have hG1 : G 1 ≠ 0 := by simp [G, hb1]
  have hGpos : 0 < ∫ z : ℂ, G z :=
    integral_pos_of_integrable_nonneg_nonzero hGcont
      (hGcont.integrable_of_hasCompactSupport hGcompact) hGnonneg hG1
  have hmoment (z : ℂ) :
      f z * (Complex.normSq z : ℂ) ^ (-(1 / 6 : ℂ)) = (G z : ℂ) := by
    have hpow : (Complex.normSq z : ℂ) ^ (-(1 / 6 : ℂ)) =
        ((Complex.normSq z ^ (-(1 / 6 : ℝ)) : ℝ) : ℂ) := by
      convert (Complex.ofReal_cpow (Complex.normSq_nonneg z) (-(1 / 6 : ℝ))).symm
        using 1 <;> norm_num
    rw [hf, hpow]
    simp only [G, Complex.ofReal_mul]
  refine ⟨f, hcompact, ?_, ?_, ?_, ?_⟩
  · intro z hz hz0
    apply hb0
    have hz' : z ∈ tsupport h := hz
    rw [htsupport] at hz'
    simpa only [hz0] using hz'
  · intro z
    rw [hf]
    exact ⟨Complex.ofReal_im _, by simpa only [Complex.ofReal_re] using b.nonneg' z⟩
  · change 0 < (∫ z : ℂ, (b z : ℂ)).re
    rw [integral_complex_ofReal, Complex.ofReal_re]
    exact hBpos
  · simp_rw [hmoment]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    exact hGpos

end ArtinPrimitiveRoots.Proofs.a2_weights_sol
