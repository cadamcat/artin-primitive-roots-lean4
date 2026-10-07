import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Primitive additive characters on every finite ideal residue ring, including
O_F/O_F. Use the trace/different pairing or finite Frobenius duality.
Guide: sol-thin-a2zf/PROOFS.md:694–701.
Uses exact nonzero exterior ideals; feeds the finite Fourier and additive estimates. -/
theorem conductor_additive_characters_exists (S : A1.SData F CE condη) :
    Nonempty (ConductorAdditiveCharacters S) := by
  sorry

end ArtinPrimitiveRoots.A2
