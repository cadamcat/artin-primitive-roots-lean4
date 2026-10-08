import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The reconstructed sums agree with the adelic series on the baseline ball, are analytic
on the continuation domain, and have the prescribed scalar Laurent fields at every point.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:809–812`.
Uses component/reconstruction data, `Spec.ContinuedEisenstein.E_series`, its Banach-valued
`E_analytic` and `laurent` at derivative order zero. Consumed by `exists_continuedEis`. -/
theorem continuedEis_series_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) :
    (∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ g,
      R.E s g = eisenstein P G (I.sec s) g) ∧
    (∀ g, AnalyticOnNhd ℂ (fun s => R.E s g)
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε)) ∧
    ∀ g, ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) C.ε) ∧
      Ψ (1 / 6) = R.theta g ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) C.ε,
        s ≠ 1 / 6 → Ψ s = (s - 1 / 6) * R.E s g := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
