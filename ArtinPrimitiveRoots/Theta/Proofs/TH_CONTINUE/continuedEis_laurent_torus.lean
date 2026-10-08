import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Commute the residue with every bounded measurable torus integral. Pull each spectral
Banach-valued Laurent field back along the fixed torus chart on closure(Pd), form the finite
analytic sum with the coefficient functions, and apply the continuous linear weighted
integral. The statement includes zero-volume sets and needs no period-lattice hypothesis.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:812–823`.
Uses `ContinuedEisTorusCharts` (produced by `continuedEis_torus_charts`), component data,
and `Spec.ContinuedEisenstein.laurent`; no pointwise limit interchange.
Consumed by frozen `exists_continuedEis`. LEAD part. -/
theorem continuedEis_laurent_torus {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) (hcharts : ContinuedEisTorusCharts R) :
    ∀ (g : P.tc.G) (Pd : Set (InfinitePlace F → ℂ)), Bornology.IsBounded Pd →
      MeasurableSet Pd → ∀ ν : F, ∃ Ψ : ℂ → ℂ,
        AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) C.ε) ∧
        Ψ (1 / 6) = torusCoeff P R.theta g Pd ν ∧
        ∀ s ∈ Metric.ball (1 / 6 : ℂ) C.ε, s ≠ 1 / 6 →
          Ψ s = (s - 1 / 6) * torusCoeff P (R.E s) g Pd ν := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
