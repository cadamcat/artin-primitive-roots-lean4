import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.primitive_conductor_residue_determines
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_gauss_orthogonality
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_additive_sieve_apply

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Transport each fixed local group injectively to its conductor/residue pair,
apply the Gauss bound and the dual additive estimate. Constants precede both lengths
and the local components. Guide: sol-thin-a2zf/PROOFS.md:666–732.
Uses primitive_conductor_residue_bridge/determines, conductor_gauss_orthogonality,
and conductor_additive_sieve_apply; feeds the dyadic Cauchy–Schwarz step. -/
theorem conductor_exterior_dyad_bound (S : A1.SData F CE condη)
    (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ T U : ℝ, 1 ≤ T → 2 ≤ U →
      ∀ (ℓ : SLocalCharacter S) (τ : ConductorInfiniteLocal F)
        (𝓧 : Finset (A1.HeckeChar F)), ConductorGroup S C₀ U ℓ τ 𝓧 →
        ∀ b : S.ExtIdeal → ℂ,
          (∑ ω ∈ 𝓧, ‖∑ I ∈ conductorExteriorDyad S T, b I * ω.idealValue I.1‖ ^ 2) ≤
            C * (T + U ^ 2) * ∑ I ∈ conductorExteriorDyad S T, ‖b I‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots.A2
