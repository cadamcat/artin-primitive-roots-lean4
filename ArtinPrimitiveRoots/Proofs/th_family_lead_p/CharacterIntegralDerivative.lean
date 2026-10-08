import ArtinPrimitiveRoots.Proofs.th_family_lead_p.PeriodicFourier
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol

/-- A smooth function's character integral can be differentiated in any fixed real direction
over a measurable domain with compact closure and finite measure. -/
theorem theta_character_integral_hasDerivAt
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (Pd : Set E) (hm : MeasurableSet Pd)
    (hcompact : IsCompact (closure Pd)) (hfinite : μ Pd ≠ ⊤)
    (f : E → ℂ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (χ : E → ℂ) (hχ : Continuous χ) (v : E) :
    IntegrableOn (fun x => fderiv ℝ f x v * χ x) Pd μ ∧
      HasDerivAt (fun t : ℝ => ∫ x in Pd, f (x + t • v) * χ x ∂μ)
        (∫ x in Pd, fderiv ℝ f x v * χ x ∂μ) 0 := by
  let : IsFiniteMeasure (μ.restrict Pd) := isFiniteMeasure_restrict.mpr hfinite
  let H : ℝ → E → ℂ := fun t x => f (x + t • v) * χ x
  let Hd : ℝ → E → ℂ := fun t x => fderiv ℝ f (x + t • v) v * χ x
  have hHc (t : ℝ) : Continuous (H t) := by
    exact (hf.continuous.comp (continuous_id.add continuous_const)).mul hχ
  have hDc : Continuous (fun p : ℝ × E => Hd p.1 p.2) := by
    exact (((hf.continuous_fderiv (by simp)).comp
      (continuous_snd.add (continuous_fst.smul continuous_const))).clm_apply
        continuous_const).mul (hχ.comp continuous_snd)
  have hD0 : Continuous (Hd 0) := by
    exact hDc.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ) 1).prod hcompact
    |>.exists_bound_of_continuousOn hDc.continuousOn
  have hH0 : Integrable (H 0) (μ.restrict Pd) :=
    (hHc 0).continuousOn.integrableOn_of_subset_isCompact hcompact hm subset_closure hfinite
  have hdiff (x : E) (t : ℝ) : HasDerivAt (fun s : ℝ => H s x) (Hd t x) t := by
    have hcurve : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id t).smul_const v).const_add x
    have hd := (hf.differentiable (by simp) (x + t • v)).hasFDerivAt.comp_hasDerivAt t
      hcurve
    simpa only [H, Hd, Function.comp_def] using
      hd.mul_const (χ x)
  have hbound : ∀ᵐ x ∂μ.restrict Pd, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      ‖Hd t x‖ ≤ C := by
    filter_upwards [ae_restrict_mem hm] with x hx t ht
    exact hC (t, x) ⟨Metric.ball_subset_closedBall ht, subset_closure hx⟩
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := H) (F' := Hd) (μ := μ.restrict Pd) (bound := fun _ => C)
    (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun t => (hHc t).aestronglyMeasurable)
    hH0 hD0.aestronglyMeasurable hbound (integrable_const C)
    (ae_of_all _ fun x t _ => hdiff x t)
  simpa only [IntegrableOn, H, Hd, zero_smul, add_zero] using hresult

end ArtinPrimitiveRoots.Proofs.majorant_sol
