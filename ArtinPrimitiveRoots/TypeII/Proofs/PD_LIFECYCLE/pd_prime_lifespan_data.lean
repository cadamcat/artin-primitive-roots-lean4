import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_lifecycle_parameters

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- The finite valid endpoint alternatives sum to the exact frozen lifespan expression.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:402–417. Uses only Defs; feeds
pd_prime_lifespan_product and history_path_value. No band or positivity assumption is needed. -/
theorem pd_prime_lifespan_data {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) :
    (∑ life : PrimeLife S γ p, primeLifeCharge F S γ p life) = pdPathLifespan F S γ p := by
  sorry

/-- Distribute the finite per-prime sums and remove the group tags using disjoint bands.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:402–417,449. Uses
pd_prime_lifespan_data and pd_lifecycle_parameters; feeds history_path_value. -/
theorem pd_prime_lifespan_product (K : ℕ) (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, x₀ ≤ S.x → ∀ γ : EnvPath S.x K,
      pdLifeChargeSum F S γ = ∏ p ∈ markedPrimes S.x K F.a, pdPathLifespan F S γ p := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
