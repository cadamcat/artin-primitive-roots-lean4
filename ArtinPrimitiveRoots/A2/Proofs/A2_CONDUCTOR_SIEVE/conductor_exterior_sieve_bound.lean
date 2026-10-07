import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_exterior_dyad_bound

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Split the finite exterior cutoff into disjoint dyads and apply
Cauchy–Schwarz, paying one logarithm. Guide: sol-thin-a2zf/PROOFS.md:733–737.
Uses conductor_exterior_dyad_bound; feeds conductor_sieve_assemble. -/
theorem conductor_exterior_sieve_bound (S : A1.SData F CE condη)
    (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ N U : ℝ, 2 ≤ N → 2 ≤ U →
      ∀ (ℓ : SLocalCharacter S) (τ : ConductorInfiniteLocal F)
        (𝓧 : Finset (A1.HeckeChar F)), ConductorGroup S C₀ U ℓ τ 𝓧 →
        ∀ b : S.ExtIdeal → ℂ,
          (∑ ω ∈ 𝓧, ‖∑ I ∈ conductorExteriorCutoff S N, b I * ω.idealValue I.1‖ ^ 2) ≤
            C * (N + U ^ 2) * (1 + Real.log N) *
              ∑ I ∈ conductorExteriorCutoff S N, ‖b I‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots.A2
