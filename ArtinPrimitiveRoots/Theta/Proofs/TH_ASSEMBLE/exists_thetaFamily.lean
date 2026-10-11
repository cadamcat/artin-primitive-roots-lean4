import ArtinPrimitiveRoots.Theta.Proofs.TH_ASSEMBLE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Assemble every field of ThetaFamily from the actual normalized common-section functions.
Uses all TH_FAMILY_FIELDS exports and
ThetaFamilyUpstream; no further analytic or topological premise is left for the consumer. -/
def thetaFamily_from_normalized_sections {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) (N : ThetaNormalizationInput P)
    (𝓛 : Finset (SChar S)) (B : ThetaCommonSections P N 𝓛)
    (Q : ThetaFamilyUpstream B) : ThetaFamily P.tc 𝓛 where
  topology := P.tc.topology
  topology_spec := rfl
  θ := thetaFamilyTheta B
  θN := thetaFamilyThetaN B
  W := thetaFamilyW B
  WS := thetaFamilyW B
  Wv := thetaExteriorWv P N.G N.μ
  genuine := fun L hL => (theta_automorphic_fields B Q.action L hL).1
  automorphic := fun L hL => (theta_automorphic_fields B Q.action L hL).2.1
  right_Kext := fun L hL => (theta_automorphic_fields B Q.action L hL).2.2
  cont := fun L hL => (theta_translation_regular_fields hRP B L hL).1
  archSmooth := fun L hL => (theta_translation_regular_fields hRP B L hL).2.1
  jointRootSmooth := fun L hL => (theta_translation_regular_fields hRP B L hL).2.2
  fourier := fun L hL g => theta_fourier_expansion hRP B Q L hL g
  fourierLocallyUniform := fun L hL K hK ε hε =>
    theta_fourierLocallyUniform hRP B Q L hL
      (fun g => theta_fourier_expansion hRP B Q L hL g) K hK ε hε
  θN_left := fun L hL => (thetaN_fields hRP B L hL).1
  θN_right := fun L hL => (thetaN_fields hRP B L hL).2.1
  θN_genuine := fun L hL => (thetaN_fields hRP B L hL).2.2.1
  cont_N := fun L hL => (thetaN_fields hRP B L hL).2.2.2.1
  factor := fun L hL ν ε gS hgS T hT g hg => theta_family_factor B Q.factor L hL ν ε gS hgS T hT g hg
  Wv_genuine := Q.exterior.1
  Wv_equiv := Q.exterior.2.1
  Wv_right := Q.exterior.2.2.1
  Wv_table := Q.exterior.2.2.2
  WS_equiv := fun L hL => (theta_WS_fields B L hL).1
  WS_genuine := fun L hL => (theta_WS_fields B L hL).2
  U := thetaCommonU B
  U_spec := theta_common_U_spec B
  cS := fun _ => 4 * Real.pi
  cS_pos := fun _ => by positivity
  T5 := fun L hL y => theta_complex_derivative_normalization B Q L hL y
  δ := 1 / 3
  δ_pos := by norm_num
  T6 := fun L hL => theta_T6_sheet_bound B Q L hL
  T7 := fun L hL => (thetaN_fields hRP B L hL).2.2.2.2
end ArtinPrimitiveRoots.A1.Theta
