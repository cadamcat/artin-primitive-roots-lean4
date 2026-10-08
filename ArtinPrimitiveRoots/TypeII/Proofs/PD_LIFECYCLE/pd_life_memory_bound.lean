import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_active_run_count

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- A lifespan assignment has at most KN pending non-ghost primes at every tested state.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:454–467. Uses pd_active_run_count;
feeds pd_truncation_choice_majorant. In each group the union of active primes has cardinal
at most M+N; remove the M current active primes and add at most the ghost-birth count. -/
theorem pd_life_memory_bound (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ γ : EnvPath S.x K, IsEnvPathAdmissible F S γ → pathCoefficient F S γ ≠ 0 →
          ∀ H : PDLifeAssignment F S γ,
            pdLifeMaxMemory F S γ H ≤ K * pathLength S.x + pdLifeGhostBirths F S γ H := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
