import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Equality up to a scalar on the convergence ball gives the same scalar relation between
residues. Both functions are analytic on the same connected punctured domain.
Guide: sol-thin-thglobal/PROOFS.md:862–882. Uses Spec.C1_domain and analytic uniqueness.
Feeds Fourier domain independence, diagonal transport, equivariance, and regularized_residue_eval. -/
theorem analytic_residue_unique (η : ℝ) (hη : 0 < η)
    (f f' : ℂ → ℂ) (r r' q : ℂ)
    (hf : AnalyticOnNhd ℂ f (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η))
    (hf' : AnalyticOnNhd ℂ f' (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η))
    (hr : ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) η) ∧
      Ψ (1 / 6) = r ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * f s)
    (hr' : ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) η) ∧
      Ψ (1 / 6) = r' ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * f' s)
    (heq : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), f s = q * f' s) :
    r = q * r' := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
