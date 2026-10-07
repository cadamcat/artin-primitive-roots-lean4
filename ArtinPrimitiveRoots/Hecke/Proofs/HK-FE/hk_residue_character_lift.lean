import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs


set_option autoImplicit false
open NumberField ClassFieldTheory
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Construct a residue character by prime-to integral lifts. Guide:
sol-thin-hk2/PROOFS.md:1209–1230. Uses H1's residue/congruence bridge and MulChar.ofUnitHom;
at the unit ideal choose the integral lift 1 explicitly. -/
theorem hk_residue_character_lift [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) :
    ∃ χ₀ : MulChar (HKResidueRing m) ℂ, ∀ a : 𝓞 K,
      IsCoprimeTo m (Ideal.span {a}) →
        χ₀ (Ideal.Quotient.mk (modulusIdeal m) a) = charValue ψ (Ideal.span {a}) := by
  sorry

end ArtinPrimitiveRoots.Hecke
