import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.FourierCoefficients
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
open MeasureTheory
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

/-- A smooth bounded interval family has continuous, uniformly absolutely summable
Fourier coefficients, with the same row support and pointwise interval reconstruction. -/
theorem fourierCoeffOn_smooth_family {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (lo hi : ℝ) (hlohi : lo < hi)
    (f : ℝ → X → ℂ) (M0 M2 : ℝ) (hM0 : 0 ≤ M0) (hM2 : 0 ≤ M2)
    (hsmooth : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => f u x))
    (hcontinuous : Continuous (fun p : ℝ × X => f p.1 p.2))
    (hcontinuous2 : Continuous (fun p : ℝ × X =>
      iteratedDeriv 2 (fun u => f u p.2) p.1))
    (hbound : ∀ x u, u ∈ Set.Icc lo hi → ‖f u x‖ ≤ M0 ∧
      ‖iteratedDeriv 2 (fun v => f v x) u‖ ≤ M2)
    (hend : ∀ x, f lo x = 0 ∧ f hi x = 0 ∧
      deriv (fun u => f u x) lo = 0 ∧ deriv (fun u => f u x) hi = 0)
    (K : Set X) (hzero : ∀ x, x ∉ K → ∀ u, f u x = 0) :
    ∃ bound : ℤ → ℝ, (∀ j, 0 ≤ bound j) ∧ Summable bound ∧
      (∀ j, Continuous (fun x => fourierCoeffOn hlohi (fun u => f u x) j)) ∧
      (∀ j x, ‖fourierCoeffOn hlohi (fun u => f u x) j‖ ≤ bound j) ∧
      (∀ j x, x ∉ K → fourierCoeffOn hlohi (fun u => f u x) j = 0) ∧
      ∀ x u, u ∈ Set.Icc lo hi →
        HasSum (fun j : ℤ => fourierCoeffOn hlohi (fun t => f t x) j *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
            (u : ℂ) / ((hi - lo : ℝ) : ℂ))) (f u x) := by
  letI : Fact (0 < hi - lo) := ⟨sub_pos.mpr hlohi⟩
  have huIcc (u : ℝ) (hu : u ∈ Set.uIcc lo hi) : u ∈ Set.Icc lo hi := by
    simpa only [Set.uIcc_of_le hlohi.le] using hu
  have hdiff (x : X) : Differentiable ℝ (fun u => f u x) :=
    (hsmooth x).differentiable (by simp)
  have hdiff1 (x : X) : Differentiable ℝ (deriv (fun u => f u x)) :=
    ((hsmooth x).of_le (by simp)).differentiable_deriv_two
  obtain ⟨bound, hnonneg, hsum, hcoeff⟩ := fourierCoeffOn_uniform_summable lo hi hlohi
    (fun x u => f u x) (fun x => deriv (fun u => f u x))
    (fun x => iteratedDeriv 2 (fun u => f u x)) M0 M2 hM0 hM2
    (fun x u _ => (hdiff x u).hasDerivAt)
    (fun x u _ => by
      simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero]
        using (hdiff1 x u).hasDerivAt)
    (fun x => (hcontinuous2.comp (continuous_id.prodMk continuous_const)).continuousOn)
    (fun x => (hend x).2.1.trans (hend x).1.symm)
    (fun x => (hend x).2.2.2.trans (hend x).2.2.1.symm)
    (fun x u hu => (hbound x u (huIcc u hu)).1)
    (fun x u hu => (hbound x u (huIcc u hu)).2)
  refine ⟨bound, hnonneg, hsum, ?_, (fun j x => hcoeff x j), ?_, ?_⟩
  · intro j
    let g : X → ℝ → ℂ := fun x u => fourier (-j) (u : AddCircle (hi - lo)) * f u x
    have hphase : Continuous (fun u : ℝ => fourier (-j) (u : AddCircle (hi - lo))) :=
      (fourier (-j)).continuous.comp (AddCircle.continuous_mk' (hi - lo))
    have hgmeas (x : X) : AEStronglyMeasurable (g x) (volume.restrict (Set.Ioc lo hi)) :=
      (hphase.mul (hsmooth x).continuous).aestronglyMeasurable
    have hgbound (x : X) : ∀ᵐ u ∂(volume.restrict (Set.Ioc lo hi)), ‖g x u‖ ≤ M0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      change ‖fourier (-j) (u : AddCircle (hi - lo)) * f u x‖ ≤ M0
      rw [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
      exact (hbound x u (Set.Ioc_subset_Icc_self hu)).1
    have hMInt : Integrable (fun _ : ℝ => M0) (volume.restrict (Set.Ioc lo hi)) :=
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M0) volume lo hi).1
    have hgcont : ∀ᵐ u ∂(volume.restrict (Set.Ioc lo hi)), Continuous (fun x => g x u) := by
      filter_upwards with u
      exact continuous_const.mul (hcontinuous.comp (continuous_const.prodMk continuous_id))
    have hInt := continuous_of_dominated hgmeas hgbound hMInt hgcont
    convert hInt.const_smul (1 / (hi - lo) : ℝ) using 1
    funext x
    simp only [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le hlohi.le,
      smul_eq_mul, Pi.smul_apply, g]
  · intro j x hx
    have heq : (fun u => f u x) = (0 : ℝ → ℂ) := funext (hzero x hx)
    rw [heq]
    simp [fourierCoeffOn_eq_integral]
  · intro x u hu
    have hcoeffSum : Summable (fourierCoeffOn hlohi (fun t => f t x)) :=
      hsum.of_norm_bounded (hcoeff x)
    exact fourierCoeffOn_reconstruct lo hi hlohi (fun t => f t x)
      (hsmooth x).continuous.continuousOn ((hend x).1.trans (hend x).2.1.symm)
      hcoeffSum u hu

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
