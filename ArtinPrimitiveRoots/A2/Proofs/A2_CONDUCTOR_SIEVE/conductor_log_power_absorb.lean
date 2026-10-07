import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Absorb any fixed logarithmic power into an arbitrarily small positive
loss, uniformly for N,U at least two. Guide: sol-thin-a2zf/PROOFS.md:737–740.
Uses elementary exponential domination; feeds conductor_sieve_assemble. -/
theorem conductor_log_power_absorb (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ N U : ℝ, 2 ≤ N → 2 ≤ U →
        (1 + Real.log N) ^ k ≤ C * Real.rpow (N * U) ε := by
  sorry

end ArtinPrimitiveRoots.A2
