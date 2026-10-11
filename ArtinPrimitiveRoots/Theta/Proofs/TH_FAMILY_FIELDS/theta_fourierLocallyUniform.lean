import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_compact_fourier_majorant
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Convert the single compact majorant and the exact Fourier identity into the consumer finite-tail estimate, in the cover topology.
Uses theta_compact_fourier_majorant and the supplied theta_fourier_expansion conclusion. -/
theorem theta_fourierLocallyUniform {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B)
    (L : SChar S) (hL : L ∈ 𝓛)
    (hFourier : ∀ g, Summable (fun ν : Fˣ => thetaFamilyW B L (P.tc.rat (diagGL ν) * g)) ∧
      thetaFamilyTheta B L g = thetaFamilyThetaN B L g +
        ∑' ν : Fˣ, thetaFamilyW B L (P.tc.rat (diagGL ν) * g))
    (K : Set P.tc.G) (hK : @IsCompact P.tc.G P.tc.topology K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F₀ : Finset Fˣ, ∀ F' : Finset Fˣ, F₀ ⊆ F' → ∀ g ∈ K,
      ‖thetaFamilyTheta B L g - thetaFamilyThetaN B L g -
        ∑ ν ∈ F', thetaFamilyW B L (P.tc.rat (diagGL ν) * g)‖ < ε := by
  obtain ⟨M, hM_nonneg, hM_summable, hM_bound⟩ :=
    theta_compact_fourier_majorant hRP B Q L hL K hK
  let f : Fˣ → P.tc.G → ℂ :=
    fun ν g => thetaFamilyW B L (P.tc.rat (diagGL ν) * g)
  have hsum_bound : ∀ ν g, g ∈ K → ‖f ν g‖ ≤ M ν := by
    intro ν g hg
    exact hM_bound ν g hg
  have huniform : TendstoUniformlyOn
      (fun t : Finset Fˣ => fun g => ∑ ν ∈ t, f ν g)
      (fun g => ∑' ν, f ν g) atTop K :=
    tendstoUniformlyOn_tsum hM_summable hsum_bound
  obtain ⟨F₀, hF₀⟩ :=
    eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.mp huniform) ε hε)
  refine ⟨F₀, ?_⟩
  intro F' hF₀F' g hg
  have hdist := hF₀ F' hF₀F' g hg
  have hid := hFourier g
  have hrewrite :
      thetaFamilyTheta B L g - thetaFamilyThetaN B L g -
          ∑ ν ∈ F', thetaFamilyW B L (P.tc.rat (diagGL ν) * g) =
        (∑' ν, f ν g) - ∑ ν ∈ F', f ν g := by
    dsimp [f]
    rw [hid.2]
    abel
  rw [hrewrite]
  simpa only [dist_eq_norm] using hdist
end ArtinPrimitiveRoots.A1.Theta
