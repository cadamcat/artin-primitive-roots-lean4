import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Choose one product neighborhood in sixth powers and all character kernels, and its analytic big-cell family.
Guide: sol-thin-thglobal/PROOFS.md:1173–1180.
Uses ThetaNormalizationInput, exists_T5_section and exists_continuedEis. -/
theorem theta_T5_common_sections (P : CoverPackage D S H A)
    (N : ThetaNormalizationInput P) (𝓛 : Finset (SChar S)) :
    Nonempty (ThetaCommonSections P N 𝓛) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
