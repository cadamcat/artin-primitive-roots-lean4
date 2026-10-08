import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_prime_lifespan_data
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_active_run_count

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Uniform explicit product bound with one factor two per ghost birth. Orphan endpoints
are bounded by the geometric hit series; active endpoints by their finite cardinality.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:482–503. Uses pd_lifecycle_parameters and
pd_active_run_count; feeds pd_truncation_tail_absorb. The b-prime denominators are already
inside the majorant, so no baseline factor is lost. -/
theorem pd_doubled_lifespan_bound (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ γ : EnvPath S.x K, IsContributingPath F S γ →
          doubledLifeMajorant F S γ ≤
            (2 * ((pathLength S.x : ℝ) + 2) ^ 2) ^ (K * (slotCount S.x + pathLength S.x)) *
              Real.exp (8 * (K : ℝ) * Real.log 2 / (1 - Real.sqrt F.q_d) *
                ((pathLength S.x : ℝ) + 1)) := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
