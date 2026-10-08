import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs
import Mathlib.Analysis.Analytic.Uniqueness

set_option autoImplicit false

namespace ArtinPrimitiveRoots.A1.Theta

/-- Scalar identity theorem for component expressions, including finite linear combinations:
agreement on the series ball gives agreement on the common continuation domain and equal
residues. This is independent of the particular adelic family.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:797–808`.
Uses frozen `Spec.isOpen_contDomain` and `Spec.isPreconnected_contDomain`.
Consumed by `continuedEis_component_reconstruction`; no continuation-existence input. -/
theorem continuedEis_component_unique (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε')
    (E E' : ℂ → ℂ) (theta theta' : ℂ)
    (hE : AnalyticOnNhd ℂ E (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε))
    (hE' : AnalyticOnNhd ℂ E' (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε'))
    (hseries : Set.EqOn E E' (Metric.ball (5 / 2 : ℂ) (1 / 2)))
    (hlaurent : ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) ε) ∧
      Ψ (1 / 6) = theta ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) ε,
        s ≠ 1 / 6 → Ψ s = (s - 1 / 6) * E s)
    (hlaurent' : ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) ε') ∧
      Ψ (1 / 6) = theta' ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) ε',
        s ≠ 1 / 6 → Ψ s = (s - 1 / 6) * E' s) :
    Set.EqOn E E' (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) (min ε ε')) ∧
      theta = theta' := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
