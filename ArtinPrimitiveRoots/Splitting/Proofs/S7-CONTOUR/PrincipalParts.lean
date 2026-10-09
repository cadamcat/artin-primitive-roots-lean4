import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open scoped Topology
open Filter

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

theorem weighted_logderiv_principal (F W : ℂ → ℂ) (p : ℂ) (m : ℤ)
    (hF : MeromorphicAt F p) (hm : meromorphicOrderAt F p = (m : WithTop ℤ))
    (hW : AnalyticAt ℂ W p) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧
      ∀ᶠ z in 𝓝[≠] p,
        (-(deriv F z) / F z) * W z = (-(m : ℂ) * W p) / (z - p) + R z := by
  obtain ⟨g, hg, hg₀, hfg⟩ := (meromorphicOrderAt_eq_int_iff hF).mp hm
  have heq : F =ᶠ[𝓝[≠] p] (fun z : ℂ => (z - p) ^ m * g z) := by
    filter_upwards [hfg] with z hz
    simpa only [smul_eq_mul] using hz
  have hlog := logDeriv_congr_nhdsNE heq
  have hds : AnalyticAt ℂ (dslope W p) p := by
    obtain ⟨q, hq⟩ := hW
    exact ⟨q.fslope, hq.has_fpower_series_dslope_fslope⟩
  let R : ℂ → ℂ := fun z => (-(deriv g z) / g z) * W z - (m : ℂ) * dslope W p z
  have hR : AnalyticAt ℂ R p :=
    ((hg.deriv.neg.div hg hg₀).mul hW).sub (analyticAt_const.mul hds)
  refine ⟨R, hR, ?_⟩
  have hgne : ∀ᶠ z in 𝓝[≠] p, g z ≠ 0 :=
    (hg.continuousAt.eventually_ne hg₀).filter_mono nhdsWithin_le_nhds
  have hga : ∀ᶠ z in 𝓝[≠] p, AnalyticAt ℂ g z :=
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hpne : ∀ᶠ z in 𝓝[≠] p, z ≠ p := self_mem_nhdsWithin
  filter_upwards [hlog, hgne, hga, hpne] with z hlogz hgz hgaz hzp
  have hsub : z - p ≠ 0 := sub_ne_zero.mpr hzp
  have hdsub : DifferentiableAt ℂ (fun w : ℂ => w - p) z :=
    differentiableAt_id.sub_const p
  have hdsub' : deriv (fun w : ℂ => w - p) z = 1 :=
    ((hasDerivAt_id z).sub_const p).deriv
  have hmodel : logDeriv F z = (m : ℂ) / (z - p) + deriv g z / g z := by
    rw [hlogz, logDeriv_fun_mul (f := fun w : ℂ => (w - p) ^ m) (g := g)
      z (zpow_ne_zero m hsub) hgz (hdsub.zpow (Or.inl hsub)) hgaz.differentiableAt,
      logDeriv_fun_zpow hdsub m]
    simp only [logDeriv_apply, hdsub', mul_one_div]
  rw [neg_div, ← logDeriv_apply F z, hmodel]
  dsimp only [R]
  rw [dslope_of_ne W hzp, slope_def_field]
  field_simp [hsub, hgz]
  ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
