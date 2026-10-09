import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false

open MeasureTheory Filter Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

theorem bounded_integral_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsLocallyFiniteMeasure μ]
    (f : E × ℂ → ℂ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Pd : Set E) (hb : Bornology.IsBounded Pd) (hm : MeasurableSet Pd) :
    IntegrableOn (fun x => fderiv ℝ (fun z : ℂ => f (x, z)) 0) Pd μ ∧
      HasFDerivAt (fun z : ℂ => ∫ x in Pd, f (x, z) ∂μ)
        (∫ x in Pd, fderiv ℝ (fun z : ℂ => f (x, z)) 0 ∂μ) 0 := by
  let L : ℂ →L[ℝ] (E × ℂ) := ContinuousLinearMap.inr ℝ E ℂ
  let DF : E × ℂ → (ℂ →L[ℝ] ℂ) := fun p => (fderiv ℝ f p).comp L
  have hDF : Continuous DF :=
    (hf.continuous_fderiv (by simp)).clm_comp_const L
  have hSlice (x : E) (z : ℂ) :
      HasFDerivAt (fun t : ℂ => f (x, t)) (DF (x, z)) z := by
    have hA : HasFDerivAt (fun t : ℂ => (x, t)) L z := by
      simpa only [L, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
        add_zero, zero_add] using
        (L.hasFDerivAt (x := z)).const_add (x, (0 : ℂ))
    exact (hf.differentiable (by simp) (x, z)).hasFDerivAt.comp z hA
  have hDf (x : E) :
      fderiv ℝ (fun z : ℂ => f (x, z)) 0 = DF (x, 0) :=
    (hSlice x 0).fderiv
  have hK : IsCompact (closure Pd) := hb.isCompact_closure
  have hInt (z : ℂ) : IntegrableOn (fun x => f (x, z)) Pd μ := by
    have hc : Continuous (fun x : E => f (x, z)) :=
      hf.continuous.comp (continuous_id.prodMk continuous_const)
    exact (hc.continuousOn.integrableOn_compact hK).mono_set subset_closure
  have hDInt (z : ℂ) : IntegrableOn (fun x => DF (x, z)) Pd μ := by
    have hc : Continuous (fun x : E => DF (x, z)) :=
      hDF.comp (continuous_id.prodMk continuous_const)
    exact (hc.continuousOn.integrableOn_compact hK).mono_set subset_closure
  obtain ⟨B, hB⟩ :=
    (hK.prod (isCompact_closedBall (0 : ℂ) 1)).exists_bound_of_continuousOn
      hDF.continuousOn
  have hBoundInt : IntegrableOn (fun _ : E => B) Pd μ :=
    (continuous_const.continuousOn.integrableOn_compact hK).mono_set subset_closure
  have hDer : HasFDerivAt (fun z : ℂ => ∫ x in Pd, f (x, z) ∂μ)
      (∫ x in Pd, DF (x, 0) ∂μ) 0 := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
      (Eventually.of_forall fun z => (hInt z).aestronglyMeasurable)
      (hInt 0) (hDInt 0).aestronglyMeasurable ?_ hBoundInt
      (Eventually.of_forall fun x z _ => hSlice x z)
    filter_upwards [ae_restrict_mem hm] with x hx
    intro z hz
    exact hB (x, z) ⟨subset_closure hx, Metric.ball_subset_closedBall hz⟩
  refine ⟨?_, ?_⟩
  · simpa only [hDf] using hDInt 0
  · simpa only [hDf] using hDer

end ArtinPrimitiveRoots.Proofs.thsol_torusf
