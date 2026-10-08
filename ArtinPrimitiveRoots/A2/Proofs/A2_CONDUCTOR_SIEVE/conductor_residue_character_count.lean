import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Finite abelian duality bounds any set of residue multiplicative characters
by the unit-group order and hence by the ring order. Works for the unit ring.
Guide: sol-thin-a2zf/PROOFS.md:712–719,742–747.
Uses MulChar/Duality; feeds the bottom-ideal family count. -/
theorem conductor_residue_character_count {R : Type*} [CommRing R] [Fintype R]
    (𝓧 : Finset (MulChar R ℂ)) :
    𝓧.card ≤ Fintype.card Rˣ ∧ Fintype.card Rˣ ≤ Fintype.card R := by
  sorry

end ArtinPrimitiveRoots.A2
