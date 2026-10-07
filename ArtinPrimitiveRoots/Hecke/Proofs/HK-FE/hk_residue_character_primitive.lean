import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_residue_character_lift


set_option autoImplicit false
open NumberField ClassFieldTheory
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Exact ray primitivity forces ideal primitivity of the residue character. Guide:
sol-thin-hk2/PROOFS.md:1231–1260. Uses hk_residue_character_lift, the smaller finite-modulus
construction and the fractional-principal congruence bridge from HK-DICT-RAY. -/
theorem hk_residue_character_primitive [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hp : HKPrimitive ψ)
    (χ₀ : MulChar (HKResidueRing m) ℂ)
    (hχ₀ : ∀ a : 𝓞 K, IsCoprimeTo m (Ideal.span {a}) →
      χ₀ (Ideal.Quotient.mk (modulusIdeal m) a) = charValue ψ (Ideal.span {a})) :
    OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ₀ := by
  sorry

end ArtinPrimitiveRoots.Hecke
