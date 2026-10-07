import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.ideal_S_exterior_split_count
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.sComponent_sign_partition
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_exterior_sieve_bound
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_family_card_bound
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_log_power_absorb

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Assemble the exact nonzero S-piece partition and local groups, absorb the
logarithms, and split off the bottom ideal using its quadratic family count.
Guide: sol-thin-a2zf/PROOFS.md:733–751.
Uses ideal_S_exterior_split_count, sComponent_sign_partition,
conductor_exterior_sieve_bound, conductor_family_card_bound, conductor_log_power_absorb.
Consumer: the exact frozen lem_conductor_sieve; no bottom multiplicativity is used. -/
theorem conductor_sieve_assemble (S : A1.SData F CE condη)
    (C₀ : ℝ) (hC₀ : 0 < C₀) (𝓛S : Finset (SLocalCharacter S)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ N U : ℝ, 2 ≤ N → 2 ≤ U →
        ∀ 𝓧 : Finset (A1.HeckeChar F), ConductorFamily S C₀ U 𝓛S 𝓧 →
          ∀ b : Ideal (𝓞 F) → ℂ,
            (∑ ω ∈ 𝓧, ‖∑ I ∈ conductorIdealCutoff F N, b I * ω.idealValue I‖ ^ 2) ≤
              C * (N + U ^ 2) * Real.rpow (N * U) ε *
                ∑ I ∈ conductorIdealCutoff F N, ‖b I‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots.A2
