import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.Defs

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- Every prescribed value at `g` that is an `orderOf g`th root of unity has
`|G| / orderOf g` character extensions. Guide: ../sol-thin-s7/PROOFS.md:328–365.
Uses Mathlib finite abelian duality; feeds `prod_one_sub_character`. -/
theorem character_evaluation_fiber_card (G : Type*) [CommGroup G] [Finite G]
    (g : G) (ζ : ℂˣ) (hζ : ζ ^ orderOf g = 1) :
    Nat.card {χ : G →* ℂˣ // χ g = ζ} = Nat.card G / orderOf g := by
  sorry

end ArtinPrimitiveRoots.Splitting
end
