import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The finite Gauss expansion and ALL unit-character orthogonality bound a
subset of primitive characters. The unit residue ring is included.
Guide: sol-thin-a2zf/PROOFS.md:702–719.
Uses OAI primitive_character_expansion and primitive_gaussSum_norm_sq; feeds dyad glue. -/
theorem conductor_gauss_orthogonality {R ι : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (𝓧 : Finset (MulChar R ℂ))
    (h𝓧 : ∀ χ ∈ 𝓧, OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ)
    (B : Finset ι) (r : ι → R) (b : ι → ℂ) :
    (∑ χ ∈ 𝓧, ‖∑ I ∈ B, b I * χ (r I)‖ ^ 2) ≤
      ((Fintype.card Rˣ : ℝ) / (Fintype.card R : ℝ)) *
        ∑ d : Rˣ, ‖∑ I ∈ B, b I * ψ (r I * (d : R))‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots.A2
