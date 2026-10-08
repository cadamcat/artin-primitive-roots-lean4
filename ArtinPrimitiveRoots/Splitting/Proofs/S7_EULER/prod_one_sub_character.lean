import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.character_evaluation_fiber_card
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.prod_one_sub_rootsOfUnity

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- The abelian character Euler polynomial. Guide:
../sol-thin-s7/PROOFS.md:328–365. Uses `character_evaluation_fiber_card` and
`prod_one_sub_rootsOfUnity`; feeds `upstairs_rhp_euler_identity`. -/
theorem prod_one_sub_character (G : Type*) [CommGroup G] [Finite G]
    (g : G) (z : ℂ) :
    (∏ χ : G →* ℂˣ, (1 - (χ g : ℂ) * z)) =
      (1 - z ^ orderOf g) ^ (Nat.card G / orderOf g) := by
  sorry

end ArtinPrimitiveRoots.Splitting
end
