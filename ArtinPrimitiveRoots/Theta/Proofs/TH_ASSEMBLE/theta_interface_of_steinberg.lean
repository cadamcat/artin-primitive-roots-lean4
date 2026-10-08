import ArtinPrimitiveRoots.Theta.Proofs.TH_ASSEMBLE.exists_thetaFamily

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- The corrected interface retains the produced CoverPackage and its canonical topology.
Guide: sol-thin-thglobal/PROOFS.md:1225–1235. Uses frozen exists_coverPackage and
the supplied exists_thetaFamily constructor, never the parked P.tc-only interface. -/
theorem theta_interface_from_family_constructor (D : FieldData F) {CE : ℕ}
    {condη : Ideal (𝓞 F)} (S : SData F CE condη) (H : HilbertData F)
    (A : AddCharData F) (hSt : ∀ v, SteinbergAt H v)
    (hFamily : ∀ P : CoverPackage D S H A, HasRestrictedProductTopology P →
      ∀ 𝓛 : Finset (SChar S), Nonempty (ThetaFamily P.tc 𝓛)) :
    ∃ P : CoverPackage D S H A, HasRestrictedProductTopology P ∧
      ∀ 𝓛 : Finset (SChar S), Nonempty (ThetaFamily P.tc 𝓛) := by
  obtain ⟨P, hRP⟩ := exists_coverPackage D S H A hSt
  exact ⟨P, hRP, hFamily P hRP⟩
end ArtinPrimitiveRoots.A1.Theta
