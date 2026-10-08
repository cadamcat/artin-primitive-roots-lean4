import ArtinPrimitiveRoots.Theta.Res
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.FourierOrbit

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Rebuild the P-SPEC component residue representation for a given family and identify its
residue pointwise with any `ContinuedEis` record for that family. -/
theorem continuedEis_spec_residue_reconstruction
    [IsTotallyComplex F] {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C0 : ContinuedEis Fam) :
    ∃ (I : ContinuedEisInput P G) (C : ContinuedEisComponents I)
      (R : ContinuedEisReconstruction C), ∀ g, R.theta g = C0.theta g := by
  let I : ContinuedEisInput P G := {
    sec := Fam.sec
    T0 := Fam.T0
    T0_eq := Fam.T0_eq
    fC_sph := Fam.fC_sph
    f_analytic := Fam.f_analytic
    level := Fam.level }
  obtain ⟨Ccomp⟩ := continuedEis_uniform_level_components I
  obtain ⟨R⟩ := continuedEis_component_reconstruction Ccomp
  obtain ⟨hseries, hanalytic, hlaurent⟩ := continuedEis_series_analytic R
  obtain ⟨hcont, harch, hjoint⟩ := continuedEis_theta_cont R
  let Cspec : ContinuedEis Fam := {
    ε := Ccomp.ε
    ε_pos := Ccomp.ε_pos
    E := R.E
    E_series := hseries
    E_analytic := hanalytic
    theta := R.theta
    laurent := hlaurent
    laurent_torus := continuedEis_laurent_torus R (continuedEis_torus_charts R)
    theta_cont := hcont
    archSmooth := harch
    jointRoots := hjoint }
  have htheta : ∀ g, R.theta g = C0.theta g := by
    intro g
    have hseriesEq : Set.EqOn (fun s => Cspec.E s g) (fun s => C0.E s g)
        (Metric.ball (5 / 2 : ℂ) (1 / 2)) := by
      intro s hs
      calc
        Cspec.E s g = eisenstein P G (Fam.sec s) g := Cspec.E_series s hs g
        _ = C0.E s g := (C0.E_series s hs g).symm
    obtain ⟨_, hres⟩ := continuedEis_component_unique
      Cspec.ε C0.ε Cspec.ε_pos C0.ε_pos
      (fun s => Cspec.E s g) (fun s => C0.E s g)
      (Cspec.theta g) (C0.theta g)
      (Cspec.E_analytic g) (C0.E_analytic g) hseriesEq
      (Cspec.laurent g) (C0.laurent g)
    exact hres
  exact ⟨I, Ccomp, R, htheta⟩

/-- The normalized family derivative is the same derivative of the reconstructed P-SPEC residue. -/
theorem thetaFamilyTheta_eq_spec_residue_deriv {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (L : SChar S)
    {I : ContinuedEisInput P N.G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) (hθ : ∀ g, R.theta g = B.C.theta g) :
    ∀ g, thetaFamilyTheta B L g =
      (thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m R.theta g := by
  intro g
  have hEq : ∀ z, R.theta (g * nInf P z) = B.C.theta (g * nInf P z) := fun z => hθ _
  have hderiv := thetaFamilyDeriv_congr_rightNInf_orbit
    L.m R.theta B.C.theta g hEq
  change (thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m B.C.theta g = _
  rw [hderiv]

end ArtinPrimitiveRoots.A1.Theta
