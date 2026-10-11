import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_residue_character_primitive


set_option autoImplicit false
open NumberField ClassFieldTheory
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Produce the primitive character on the exact finite ray residue ring, including the
unit-modulus case. Uses HK-DICT-RAY conductor
descent and H1's integral residue/congruence bridge; no ordinary ZMod character is substituted. -/
theorem hk_primitive_residue_character [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hp : HKPrimitive ψ) :
    Nonempty (HKResidueCharacter ψ) := by
  obtain ⟨χ₀, hχ₀⟩ := hk_residue_character_lift ψ
  refine ⟨⟨χ₀, hχ₀, ?_⟩⟩
  exact hk_residue_character_primitive ψ hp χ₀ hχ₀

end ArtinPrimitiveRoots.Hecke
